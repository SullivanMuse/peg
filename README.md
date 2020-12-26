# Idea

A rust macro for generating PEG parsers.

# Features

- Literals
  - strs `"Hello"`
  - chars `'c'`
  - char ranges `'0'..='9'`
- Sequence `e e`
- Alternation `e | e`
- Atomicity
  - Atomic `atomic e`
  - Non-atomic `non_atomic e`
- Lookahead
  - Negative lookahead `!e`
  - Positive lookahead `&e`
- Case sensitivity
  - Insensitive `insensitive e`
  - Sensitive `sensitive e`
- Stack manipulation
  - 

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
  = '$' // Slice
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
