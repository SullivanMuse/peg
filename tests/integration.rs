use pgen::peg;

#[test]
fn test_char_lit() {
    peg! {
        x = 'x'
    }
    let input = Input::new("x");
    assert_eq!(x(input), Some((input.advance(1), ())));
}
