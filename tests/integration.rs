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

#[test]
fn test_char_range() {
    peg! {
        x = '0'..='9'
    }
    let input = Input::new("1234");
    assert_eq!(x(input), Some((input.advance(1), ())));
}

#[test]
fn test_call() {
    peg! {
        x = '0'..='9'
        y = x
    }
    let input = Input::new("1234");
    assert_eq!(y(input), Some((input.advance(1), ())));
}

#[test]
fn test_cat() {
    peg! {
        x = '0' '1'
    }
    let input = Input::new("0101");
    assert_eq!(x(input), Some((input.advance(2), ())));
}

#[test]
fn test_many0() {
    peg! {
        x = '0'..='9'
        y = x*
    }
    let input = Input::new("1234");
    assert_eq!(y(input), Some((input.advance(4), ())));

    let input = Input::new("");
    assert_eq!(y(input), Some((input, ())));
}

#[test]
fn test_many1() {
    peg! {
        x = '0'..='9'
        y = x+
    }
    let input = Input::new("1234");
    assert_eq!(y(input), Some((input.advance(4), ())));

    let input = Input::new("");
    assert_eq!(y(input), None);
}

#[test]
fn test_optional() {
    peg! {
        x = '0'..='9'
        y = x x?
    }
    let input = Input::new("1234");
    assert_eq!(y(input), Some((input.advance(2), ())));

    let input = Input::new("1");
    assert_eq!(y(input), Some((input.advance(1), ())));

    let input = Input::new("");
    assert_eq!(y(input), None);
}

#[test]
fn test_pos() {
    peg! {
        x = 'a'..='z'
        y = &x "a1234"
    }
    let input = Input::new("a1234");
    assert_eq!(y(input), Some((input.advance(5), ())));

    let input = Input::new("asdf");
    assert_eq!(y(input), None);
}

#[test]
fn test_neg() {
    peg! {
        x = 'a'..='z'
        y = !x "1234"
    }
    let input = Input::new("1234");
    assert_eq!(y(input), Some((input.advance(4), ())));

    let input = Input::new("asdf");
    assert_eq!(y(input), None);
}
