// These test cases were taken from the `alloc` crate's test suite
// (https://github.com/rust-lang/rust/blob/c98d0cb27cc63afdd62602a52eb4feb8a1c682dd/library/alloctests/tests/str.rs)
use std::str::from_utf8;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    // deny overlong encodings
    assert!(from_utf8(&[0xc0, 0x80]).is_err());
    assert!(from_utf8(&[0xc0, 0xae]).is_err());
    assert!(from_utf8(&[0xe0, 0x80, 0x80]).is_err());
    assert!(from_utf8(&[0xe0, 0x80, 0xaf]).is_err());
    assert!(from_utf8(&[0xe0, 0x81, 0x81]).is_err());
    assert!(from_utf8(&[0xf0, 0x82, 0x82, 0xac]).is_err());
    assert!(from_utf8(&[0xf4, 0x90, 0x80, 0x80]).is_err());

    // deny surrogates
    assert!(from_utf8(&[0xED, 0xA0, 0x80]).is_err());
    assert!(from_utf8(&[0xED, 0xBF, 0xBF]).is_err());

    assert!(from_utf8(&[0xC2, 0x80]).is_ok());
    assert!(from_utf8(&[0xDF, 0xBF]).is_ok());
    assert!(from_utf8(&[0xE0, 0xA0, 0x80]).is_ok());
    assert!(from_utf8(&[0xED, 0x9F, 0xBF]).is_ok());
    assert!(from_utf8(&[0xEE, 0x80, 0x80]).is_ok());
    assert!(from_utf8(&[0xEF, 0xBF, 0xBF]).is_ok());
    assert!(from_utf8(&[0xF0, 0x90, 0x80, 0x80]).is_ok());
    assert!(from_utf8(&[0xF4, 0x8F, 0xBF, 0xBF]).is_ok());

    // deny invalid bytes embedded in long stretches of ascii
    for i in 32..64 {
        let mut data = [0; 128];
        data[i] = 0xC0;
        assert!(from_utf8(&data).is_err());
        data[i] = 0xC2;
        assert!(from_utf8(&data).is_err());
    }

    let xs = b"hello";
    assert!(from_utf8(xs) == Ok("hello"));

    let xs = "ศไทย中华Việt Nam".as_bytes();
    assert!(from_utf8(xs) == Ok("ศไทย中华Việt Nam"));

    let xs = b"hello\xFF";
    assert!(from_utf8(xs).is_err());
}

pub fn main() {
    println!("{:?}", crux_test());
}
