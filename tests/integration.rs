use pgen::peg;

#[test]
fn test_char_lit() {
    peg! {
        x = 'x'
    }
    let input = Input::new("x");
    assert_eq!(x(input), Some((input.advance(1), ())));
}

#[test]
fn test_str_lit() {
    peg! {
        x = "Hello"
    }
    let input = Input::new("Hello, there!");
    assert_eq!(x(input), Some((input.advance(5), ())));
}
