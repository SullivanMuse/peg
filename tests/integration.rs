use pgen::peg;

#[test]
fn test() {
    peg!{
        space = !&@hooplah* | another*+? // Hello, there!
    }
    assert!(true);
}

#[test]
fn test_atom() {
    peg! {
        space = atom | '0' | "0" | '0'..='9'
    }
}

#[test]
fn test_paren() {
    peg! {
        space = r:atom (another | another)
    }
}
