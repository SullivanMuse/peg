use std::collections::HashMap;
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Ident,
    LitChar,
    LitStr,
    parenthesized,
    parse_macro_input,
    parse::{
        Parse,
        ParseStream,
    },
    Result,
    Token,
    token::Paren,
    Type,
    Visibility,
};

#[derive(Debug, PartialEq, Eq)]
enum Atom<Key> {
    Ident(Key),
    Str(LitStr),
    Char(LitChar),
    Range(LitChar, LitChar),
    Paren(Box<Expr<Key>>),
}

impl Atom<Ident> {
    fn replace_keys(&self, map: &HashMap<Ident, usize>) -> Atom<usize> {
        match self {
            Self::Ident(ident) => Atom::Ident(*map.get(ident).expect(&format!("No rule matches the identifier: `{}`", ident))),
            Self::Str(string) => Atom::Str(string.clone()),
            Self::Char(character) => Atom::Char(character.clone()),
            Self::Range(left, right) => Atom::Range(left.clone(), right.clone()),
            Self::Paren(inner) => Atom::Paren(Box::new(inner.replace_keys(map))),
        }
    }
}

impl Parse for Atom<Ident> {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Paren) {
            let content;
            parenthesized!(content in input);
            let expr = content.parse::<Expr<Ident>>()?;
            Ok(Self::Paren(Box::new(expr)))
        } else if input.peek(Ident) {
            Ok(Self::Ident(input.parse::<Ident>()?))
        } else if input.peek(LitStr) {
            Ok(Self::Str(input.parse::<LitStr>()?))
        } else {
            let start = input.parse::<LitChar>()?;
            if input.peek(Token![..]) {
                input.parse::<Token![..]>()?;
                input.parse::<Token![=]>()?;
                let end = input.parse::<LitChar>()?;
                Ok(Self::Range(start, end))
            } else {
                Ok(Self::Char(start))
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Expr<Key> {
    Alt(Box<Self>, Box<Self>),
    Cat(Vec<(Option<Ident>, Self)>),

    // Postfix
    Many0(Box<Self>),
    Many1(Box<Self>),
    Optional(Box<Self>),

    // Prefix
    Pos(Box<Self>),
    Neg(Box<Self>),
    Atomic(Box<Self>),

    Atom(Atom<Key>),
}

impl Expr<Ident> {
    fn atom(input: ParseStream) -> Result<Self> {
        Ok(Self::Atom(input.parse::<Atom<Ident>>()?))
    }

    /// Handle prefix operators (!, &, @)
    fn prefix(input: ParseStream) -> Result<Self> {
        if input.peek(Token![!]) {
            input.parse::<Token![!]>()?;
            let inner = Self::prefix(input)?;
            Ok(Self::Neg(Box::new(inner)))
        } else if input.peek(Token![&]) {
            input.parse::<Token![&]>()?;
            let inner = Self::prefix(input)?;
            Ok(Self::Pos(Box::new(inner)))
        } else if input.peek(Token![@]) {
            input.parse::<Token![@]>()?;
            let inner = Self::prefix(input)?;
            Ok(Self::Atomic(Box::new(inner)))
        } else {
            Self::atom(input)
        }
    }

    fn postfix(input: ParseStream) -> Result<Self> {
        let mut inner = Self::prefix(input)?;
        loop {
            if input.peek(Token![*]) {
                input.parse::<Token![*]>()?;
                inner = Self::Many0(Box::new(inner));
            } else if input.peek(Token![?]) {
                input.parse::<Token![?]>()?;
                inner = Self::Optional(Box::new(inner));
            } else if input.peek(Token![+]) {
                input.parse::<Token![+]>()?;
                inner = Self::Many1(Box::new(inner));
            } else {
                break
            }
        }
        Ok(inner)
    }

    fn named(input: ParseStream) -> Result<(Option<Ident>, Self)> {
        if input.peek2(Token![:]) {
            let name = input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let expr = Self::postfix(input)?;
            Ok((Some(name), expr))
        } else {
            Ok((None, Self::postfix(input)?))
        }
    }

    fn cat(input: ParseStream) -> Result<Self> {
        let mut seq = vec![Self::named(input)?];
        while (input.peek(Ident) && !input.peek2(Token![=]) && !input.peek2(Token![->]))
            || input.peek(LitStr)
            || input.peek(LitChar)
            || input.peek(Token![!])
            || input.peek(Token![@])
            || input.peek(Token![&])
            || input.peek(Paren)
        {
            seq.push(Self::named(input)?);
        }
        Ok(Self::Cat(seq))
    }

    fn replace_keys(&self, map: &HashMap<Ident, usize>) -> Expr<usize> {
        match self {
            Self::Alt(left, right) => Expr::Alt(Box::new(left.replace_keys(map)), Box::new(right.replace_keys(map))),
            Self::Cat(inner) => Expr::Cat(inner.iter().map(|(name, inner)| (name.clone(), inner.replace_keys(map))).collect::<Vec<_>>()),
            
            // Postfix
            Self::Many0(inner) => Expr::Many0(Box::new(inner.replace_keys(map))),
            Self::Many1(inner) => Expr::Many1(Box::new(inner.replace_keys(map))),
            Self::Optional(inner) => Expr::Optional(Box::new(inner.replace_keys(map))),

            // Prefix
            Self::Pos(inner) => Expr::Pos(Box::new(inner.replace_keys(map))),
            Self::Neg(inner) => Expr::Neg(Box::new(inner.replace_keys(map))),
            Self::Atomic(inner) => Expr::Atomic(Box::new(inner.replace_keys(map))),

            Self::Atom(atom) => Expr::Atom(atom.replace_keys(map)),
        }
    }
}

impl Parse for Expr<Ident> {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut left = Self::cat(input)?;
        while input.peek(Token![|]) {
            input.parse::<Token![|]>()?;
            let right = Self::cat(input)?;
            left = Self::Alt(Box::new(left), Box::new(right));
        }
        Ok(left)
    }
}

#[derive(Debug)]
struct Rule<Key> {
    vis: Option<Visibility>,
    name: Key,
    ty: Option<Type>,
    expr: Expr<Key>,

    is_left_rec: bool,
}

impl Rule<Ident> {
    fn replace_keys(&self, map: &HashMap<Ident, usize>) -> Rule<usize> {
        Rule::<usize> {
            vis:         self.vis.clone(),
            name:        *map.get(&self.name).expect("The name of a rule never made it into the map."),
            ty:          self.ty.clone(),
            expr:        self.expr.replace_keys(map),
            is_left_rec: self.is_left_rec,
        }
    }
}

impl Parse for Rule<Ident> {
    fn parse(input: ParseStream) -> Result<Self> {
        let vis = if !input.peek(Ident) {
            Some(input.parse::<Visibility>()?)
        } else {
            None
        };
        let name = input.parse::<Ident>()?;
        let ty = if input.peek(Token![->]) {
            input.parse::<Token![->]>()?;
            Some(input.parse::<Type>()?)
        } else {
            None
        };
        input.parse::<Token![=]>()?;
        let expr = input.parse::<Expr<Ident>>()?;
        let is_left_rec = false;
        Ok(Self { vis, name, ty, expr, is_left_rec })
    }
}

#[derive(Debug)]
struct Grammar {
    rules: Vec<Rule<Ident>>,
}

impl Grammar {
    fn to_compiler(&self) -> Compiler {
        use std::collections::HashSet;
        let mut counter = 0;
        let mut names = HashSet::new();
        let mut indices = HashMap::new();
        let mut reverse = HashMap::new();
        let mut space_defined = false;
        for rule in self.rules.iter() {
            if rule.name.to_string().ends_with("__atomic") {
                panic!("Rule names may not end with `__atomic`.");
            }
            if rule.name.to_string().as_str() == "space" {
                space_defined = true;
            }
            if names.contains(&rule.name) {
                panic!("Two rules with the same name: {}", &rule.name);
            } else {
                names.insert(rule.name.clone());
                indices.insert(counter, rule.name.clone());
                reverse.insert(rule.name.clone(), counter);
                counter += 1;
            }
        }
        let rules = self.rules.iter().map(|rule| rule.replace_keys(&reverse)).collect::<Vec<_>>();
        Compiler { rules, indices, space_defined }
    }
}

impl Parse for Grammar {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut rules = vec![];
        while input.peek(Ident) || input.peek(Token![pub]) || input.peek(Token![crate]) {
            rules.push(input.parse::<Rule<Ident>>()?);
        }
        Ok(Self { rules })
    }
}

#[derive(Debug)]
struct Compiler {
    rules: Vec<Rule<usize>>,
    indices: HashMap<usize, Ident>,

    space_defined: bool,
}

impl Compiler {
    /// Determine if rules are left recursive and modify relevant booleans
    fn left_rec(&mut self) {
        /// Helper structure
        struct Checker<'a> {
            // Basic info
            rules: &'a Vec<Rule<usize>>,
            rule: usize,
    
            // Memos
            transparent_map: HashMap<RefEq<'a, Expr<usize>>, bool>,
            left_rec_expr_map: HashMap<RefEq<'a, Expr<usize>>, bool>,
        }
    
        impl<'a> Checker<'a> {
            /// Returns whether or not a rule can consume no input
            fn transparent(&mut self, expr: &'a Expr<usize>) -> bool {
                let ref_eq = RefEq(expr);
                if let Some(result) = self.left_rec_expr_map.get(&ref_eq) {
                    return *result
                }
                let result = match expr {
                    // Alternative may consume no input if either alternative may consume no input
                    Expr::Alt(left, right)
                        => self.transparent(left)
                        || self.transparent(right),
                    
                    // Concatenation may consume no input if all rules may consume no input
                    Expr::Cat(inner) => inner.iter().all(|(_, inner)| self.transparent(inner)),
                    
                    // The following may consume no input if the inner parser may consume no input
                    Expr::Many1(inner) => self.transparent(inner),
                    Expr::Atomic(inner) => self.transparent(inner),
                    
                    // The following may consume no input unconditionally
                    Expr::Many0(_)
                    | Expr::Optional(_)
                    | Expr::Pos(_)
                    | Expr::Neg(_) => true,
    
                    // Atoms must be refined
                    Expr::Atom(atom) => match atom {
                        // A call to another rule is transparent if the rule is transparent
                        Atom::Ident(key) => {
                            let inner = &self.rules.get(*key).unwrap().expr;
                            self.transparent(inner)
                        }
    
                        // Parenthesized atoms are the result of the inner expr
                        Atom::Paren(inner) => self.transparent(inner),
    
                        // Literals must consume input
                        _ => false,
                    }
                };
                self.left_rec_expr_map.insert(ref_eq, result);
                result
            }
    
            /// Returns whether or not an expression is left recursive directly
            fn left_rec_expr(&mut self, expr: &'a Expr<usize>) -> bool {
                let ref_eq = RefEq(expr);
                if let Some(result) = self.left_rec_expr_map.get(&ref_eq) {
                    return *result
                }
                let result = match expr {
                    // An alternative is left recursive if one of the alternatives is left recursive
                    Expr::Alt(left, right)
                        => self.left_rec_expr(left)
                        || self.left_rec_expr(right),
                    
                    // A concatenation is left recursive if any of the possible starts of the concatenation are left recursive
                    Expr::Cat(inner) => {
                        for (_, inner) in inner {
                            if self.left_rec_expr(inner) {
                                return true
                            } else if !self.transparent(inner) {
                                break
                            }
                        }
                        false
                    }
    
                    // Left recursive if the inner is
                    Expr::Many1(inner)
                    | Expr::Optional(inner)
                    | Expr::Pos(inner)
                    | Expr::Neg(inner)
                    | Expr::Atomic(inner) // TODO: Fix for implicit spaces
                    | Expr::Many0(inner) => self.left_rec_expr(inner),
    
                    // Atoms MAY be left recursive
                    Expr::Atom(atom) => match atom {
                        // A call dereferences to determine if left recursive
                        Atom::Ident(key) => {
                            if *key == self.rule {
                                true
                            } else {
                                let inner = &self.rules.get(*key).unwrap().expr;
                                self.left_rec_expr(inner)
                            }
                        }
    
                        // Simple
                        Atom::Paren(inner) => self.left_rec_expr(inner),
    
                        // Literals can't be left recursive because they don't contain other rules.
                        _ => false
                    }
                };
                self.left_rec_expr_map.insert(ref_eq, result);
                result
            }
        }
    
        let left_recs = {
            let mut checker = Checker {
                rules: &self.rules,
                rule: 0,
                transparent_map: HashMap::new(),
                left_rec_expr_map: HashMap::new(),
            };
            self.rules.iter().enumerate().map(|(index, rule)| {
                checker.rule = index;
                checker.left_rec_expr(&rule.expr)
            }).collect::<Vec<_>>()
        };

        self.rules.iter_mut().zip(left_recs.into_iter()).for_each(|(rule, rec)| rule.is_left_rec = rec);
    }

    fn compile_expr(&self, expr: &Expr<usize>, atomic: bool) -> proc_macro2::TokenStream {
        match expr {
            Expr::Atom(atom) => match atom {
                Atom::Char(char_lit) => quote!((|| {
                    let curr = input.curr();
                    let rest = curr.strip_prefix(#char_lit)?;
                    let delta = curr.len() - rest.len();
                    Some((input.advance(delta), ()))
                })()),
                Atom::Str(str_lit) => quote!((|| {
                    let curr = input.curr();
                    let rest = curr.strip_prefix(#str_lit)?;
                    let delta = curr.len() - rest.len();
                    Some((input.advance(delta), ()))
                })()),
                Atom::Range(start, end) => quote!((|| {
                    let curr = input.curr();
                    let rest = curr.strip_prefix(|c: char| (#start..=#end).contains(&c))?;
                    let delta = curr.len() - rest.len();
                    Some((input.advance(delta), ()))
                })()),
                Atom::Ident(key) => {
                    let ident = if atomic {
                        let ident = self.indices.get(key).unwrap();
                        let name = format!("{}__atomic", ident.to_string());
                        Ident::new(&name, ident.span())
                    } else {
                        self.indices.get(key).unwrap().clone()
                    };
                    quote!(#ident(input))
                }
                Atom::Paren(inner) => self.compile_expr(inner, atomic),
            }
            Expr::Cat(inner) => {
                let mut q = quote!();
                let mut first = true;
                for (name, inner) in inner {
                    let name = name.as_ref().map(|name| quote!(#name)).unwrap_or(quote!(_));
                    let inner = self.compile_expr(inner, atomic);
                    q = if atomic || first {
                        first = false;
                        quote!(#q; let (input, #name) = #inner?)
                    } else {
                        quote!(
                            #q;
                            let (input, _) = space(input)?;
                            let (input, #name) = #inner?
                        )
                    };
                }
                quote!(#q; Some((input, ())))
            }
            Expr::Many0(inner) => {
                let inner = self.compile_expr(inner, atomic);
                if !atomic {
                    quote!({
                        if let Some((mut input, _)) = #inner {
                            while let Some((input1, _)) = (|input: Input<'a>| {
                                let (input, _) = space(input)?;
                                let (input, _) = #inner?;
                                Some((input, ()))
                            })(input) {
                                input = input1;
                            }
                            Some((input, ()))
                        } else {
                            Some((input, ()))
                        }
                    })
                } else {
                    quote!({
                        let mut input = input;
                        while let Some((input1, _)) = #inner {
                            input = input1;
                        }
                        Some((input, ()))
                    })
                }
            }
            Expr::Many1(inner) => {
                let inner = self.compile_expr(inner, atomic);
                quote!((|| {
                    let (mut input, _) = #inner?;
                    while let Some((input1, _)) = #inner {
                        input = input1;
                    }
                    Some((input, ()))
                })())
            }
            Expr::Optional(inner) => {
                let inner = self.compile_expr(inner, atomic);
                quote!((||
                    Some(#inner
                        .map(|(input, result)| (input, Some(result)))
                        .unwrap_or((input, None)))
                )())
            }
            Expr::Pos(inner) => {
                let inner = self.compile_expr(inner, atomic);
                quote!((|| #inner.map(|(_, result)| (input, result)))())
            }
            Expr::Neg(inner) => {
                let inner = self.compile_expr(inner, atomic);
                quote!((|| {
                    if let Some(_) = #inner {
                        None
                    } else {
                        Some((input, ()))
                    }
                })())
            }
            _ => todo!(),
        }
    }

    fn compile_rule(&self, rule: &Rule<usize>, atomic: bool) -> proc_macro2::TokenStream {
        let ret = rule.ty.as_ref().map(|ty| quote!(#ty)).unwrap_or(quote!(()));
        let ident = if atomic {
            let ident = self.indices.get(&rule.name).unwrap();
            let name = format!("{}__atomic", ident.to_string());
            Ident::new(&name, ident.span())
        } else {
            self.indices.get(&rule.name).unwrap().clone()
        };
        let expr = self.compile_expr(&rule.expr, atomic);
        quote!(
            fn #ident<'a>(input: Input<'a>) -> Option<(Input<'a>, #ret)> {
                #expr
            }
        )
    }

    fn compile(&self) -> proc_macro2::TokenStream {
        let mut q = quote!(
            #[derive(Clone, Copy, Debug, PartialEq)]
            struct Input<'a> {
                string: &'a str,
                index: usize,
            }

            impl<'a> Input<'a> {
                fn new(string: &'a str) -> Self {
                    Self { string, index: 0 }
                }

                fn advance(&self, delta: usize) -> Self {
                    let mut input = *self;
                    input.index += delta;
                    input
                }

                fn curr(&self) -> &str {
                    self.string.get(self.index..).unwrap_or("")
                }
            }
        );

        if !self.space_defined {
            q = quote!(
                #q
                fn space<'a>(input: Input<'a>) -> Option<(Input<'a>, ())> {
                    let curr = input.curr();
                    let mut rest = curr;
                    while let Some(rest1) = rest.strip_prefix(|c:char| c.is_whitespace()) {
                        rest = rest1;
                    }
                    let delta = curr.len() - rest.len();
                    let input = input.advance(delta);
                    Some((input, ()))
                }
            );
        }

        for rule in &self.rules {
            let name = self.indices.get(&rule.name).unwrap();
            let rule_atomic = self.compile_rule(rule, true);
            let rule = self.compile_rule(rule, false);
            q = quote!(#q #rule #rule_atomic);
        }
        q
    }
}

/// A structure that treats references as equal. Used for memoization in the left_rec checker
#[derive(Debug, Eq)]
struct RefEq<'a, T>(&'a T);

impl<'a, T> std::hash::Hash for RefEq<'a, T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0 as *const T).hash(state)
    }
}

impl<'a, 'b, T> PartialEq<RefEq<'b, T>> for RefEq<'a, T> {
    fn eq(&self, other: &RefEq<'b, T>) -> bool {
        self.0 as *const T == other.0 as *const T
    }
}

#[proc_macro]
pub fn peg(input: TokenStream) -> TokenStream {
    let grammar = parse_macro_input!(input as Grammar);
    let compiler = grammar.to_compiler();
    compiler.compile().into()
}

#[cfg(test)]
mod test {
    use super::*;
    use syn::parse_str;

    #[test]
    fn test_left_rec() {
        let grammar = parse_str::<Grammar>("
            x = x y
            y = y x
        ").unwrap();
        let mut compiler = grammar.to_compiler();
        compiler.left_rec();
        assert!(compiler.rules.iter().all(|rule| rule.is_left_rec));

        let grammar = parse_str::<Grammar>("
            x = '0'..='9'
            y = x y?
        ").unwrap();
        let mut compiler = grammar.to_compiler();
        compiler.left_rec();
        assert!(!compiler.rules.iter().any(|rule| rule.is_left_rec));
    }

    #[test]
    #[should_panic(expected = "Rule names may not end with `__atomic`.")]
    fn test_does_not_end_with_atomic() {
        parse_str::<Grammar>("x__atomic = 'x'")
            .unwrap()
            .to_compiler();
    }
}
