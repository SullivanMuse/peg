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

#[derive(Debug)]
enum Atom<Key> {
    Ident(Key),
    Str(LitStr),
    Char(LitChar),
    Range(LitChar, LitChar),
    Paren(Box<Expr<Key>>),
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

#[derive(Debug)]
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
        while input.peek(Ident)
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
    rules: Vec<()>,
}

#[proc_macro]
pub fn peg(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as Grammar);
    quote!().into()
}
