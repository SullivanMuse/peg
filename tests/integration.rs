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
        crate space -> Option<usize> = r:atom (another | another)
    }
}

#[test]
fn test_duplicate_rules() {
    peg! {
        x = x y
        y = y x
    }
}
