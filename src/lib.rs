use std::collections::HashMap;
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Ident,
    LitChar,
    LitStr,
    Result,
    Type,
    Token,
    Visibility,
    token::Paren,
    parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
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
    Cat(Vec<Self>),

    // Postfix
    Many0(Box<Self>),
    Many1(Box<Self>),
    Optional(Box<Self>),

    // Prefix
    Pos(Box<Self>),
    Neg(Box<Self>),
    Atomic(Box<Self>),

    Named(Ident, Box<Self>),

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

    fn named(input: ParseStream) -> Result<Self> {
        if input.peek2(Token![:]) {
            let name = input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let expr = Self::postfix(input)?;
            Ok(Self::Named(name, Box::new(expr)))
        } else {
            Self::postfix(input)
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
            Self::Cat(inner) => Expr::Cat(inner.iter().map(|inner| inner.replace_keys(map)).collect::<Vec<_>>()),
            
            // Postfix
            Self::Many0(inner) => Expr::Many0(Box::new(inner.replace_keys(map))),
            Self::Many1(inner) => Expr::Many1(Box::new(inner.replace_keys(map))),
            Self::Optional(inner) => Expr::Optional(Box::new(inner.replace_keys(map))),

            // Prefix
            Self::Pos(inner) => Expr::Pos(Box::new(inner.replace_keys(map))),
            Self::Neg(inner) => Expr::Neg(Box::new(inner.replace_keys(map))),
            Self::Atomic(inner) => Expr::Atomic(Box::new(inner.replace_keys(map))),

            Self::Named(ident, inner) => Expr::Named(ident.clone(), Box::new(inner.replace_keys(map))),

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
        for rule in self.rules.iter() {
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
        Compiler { rules, indices }
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
}

/// A structure that treats references as equal
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

/// Determine if a rule is left recursive
fn left_rec(rules: &Vec<Rule<usize>>, rule: usize) -> bool {
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
                Expr::Cat(inner) => inner.iter().all(|inner| self.transparent(inner)),
                
                // The following may consume no input if the inner parser may consume no input
                Expr::Many1(inner) => self.transparent(inner),
                Expr::Atomic(inner) => self.transparent(inner),
                Expr::Named(_, inner) => self.transparent(inner),
                
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
                    for inner in inner {
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
                | Expr::Many0(inner)
                | Expr::Named(_, inner) => self.left_rec_expr(inner),

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

    let expr = &rules.get(rule).unwrap().expr;
    Checker { rules, rule, transparent_map: HashMap::new(), left_rec_expr_map: HashMap::new() }.left_rec_expr(expr)
}

#[proc_macro]
pub fn peg(input: TokenStream) -> TokenStream {
    let grammar = parse_macro_input!(input as Grammar);
    let compiler = grammar.to_compiler();
    dbg!(left_rec(&compiler.rules, 0));
    dbg!(compiler);
    quote!().into()
}
