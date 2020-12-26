use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Ident,
    Result,
    Token,
    parse::{Parse, ParseStream},
    parse_macro_input,
};

#[derive(Debug)]
enum Expr {
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

    Call(Ident),
}

impl Expr {
    fn call(input: ParseStream) -> Result<Self> {
        Ok(Self::Call(input.parse::<Ident>()?))
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
            Self::call(input)
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

    fn cat(input: ParseStream) -> Result<Self> {
        let mut seq = vec![Self::postfix(input)?];
        while input.peek(Ident) {
            seq.push(Self::postfix(input)?);
        }
        Ok(Self::Cat(seq))
    }
}

impl Parse for Expr {
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
struct Rule {
    name: Ident,
    expr: Expr,
}

impl Parse for Rule {
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse::<Ident>()?;
        input.parse::<Token![=]>()?;
        let expr = input.parse::<Expr>()?;
        Ok(Self { name, expr })
    }
}

#[derive(Debug)]
struct Grammar {
    rules: Vec<Rule>,
}

impl Parse for Grammar {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut rules = vec![];
        while input.peek(Ident) {
            rules.push(input.parse::<Rule>()?);
        }
        Ok(Self { rules })
    }
}

#[proc_macro]
pub fn peg(input: TokenStream) -> TokenStream {
    dbg!(&input);
    dbg!(parse_macro_input!(input as Grammar));
    quote!().into()
}
