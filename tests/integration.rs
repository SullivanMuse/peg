use pgen::peg;

#[test]
fn test() {
    peg!{
        space = !&@hooplah* | another*+? // Hello, there!
    }
    assert!(true);
}
