# Idea

A rust macro for generating PEG parsers.

# Features

- Literals
  - strs `"Hello"`
  - chars `'c'`
  - char ranges `'0'..='9'`
- Span `$e`
- Atomic `@e`
- Named `name: e`
- Lookahead
  - Positive lookahead `&e`
  - Negative lookahead `!e`
- Sequence `e e`
- Alternation `e | e`
- Number
  - Many 0 (zero or more) `e*`
  - Many 1 (one or more) `e+`
  - Optional (zero or one) `e?`

# Predefined rules

```
any = // Matches any single character
digit = '0'..='9'
alpha = insensitive['a'..='z']
alnum = alpha | digit
comment = !any
space = (whitespace | comment)*
```

# Grammar

```
rule = name '=' alt
alt = cat ('|' cat)* action?
cat = (named | unary)+
named = name ':' unary
unary = prefix | postfix | atom
prefix_op
  = '$' // Span
  | '@' // Atomic
  | '!' // Negative lookahead
  | '&' // Positive lookahead
postfix_op
  = '*' // Many0
  | '+' // Many1
  | '?' // Optional
prefix = prefix_op atom
postfix = postfix_op atom
atom = name | literal | parenthesized
parenthesized = '(' alt ')'
```

# Left-Recursion

## Detection

## Runtime

Try the rule over and over, with recursion depth from 1.., until the parse fails. Now the latest cached result is the answer.

# Compilation

- Parse the syntax
- Replace all rule names with indices
- Detect overwriting of built-in rules
- Mark left-recursive rules
- Report refutable bindings

# Delim

For delimiters, we may want to select for
- 0 or more occurrences `[]`
- 1 or more occurrences `[1]`
- 1 or more occurrences, but only when there is a trailing comma `[1,]`
- When `x` has return type `X` and `y` has return type `Y`, `x ^ y` should have return type `(Vec<X>, Vec<Y>)`
- Tuple can be made as follows:

```
tuple = '(' item: item ',' items: item ^ ',' ')' {
    let mut items = items.0;
    items.insert(0, item);
    items
}
```

Alternatively

```
tuple = '(' items: item ^ ',' ')' {?
  // At least one comma
  match items.1.len() {
    0 => None
    _ => Some(items.0)
  }
}
```

# Todo
