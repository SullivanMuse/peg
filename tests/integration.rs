use pgen::peg;

#[test]
fn test() {
    peg!{
        space = hooplah* // Hello, there!
    }
    assert!(true);
}
