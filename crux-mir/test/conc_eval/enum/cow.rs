use std::borrow::Cow;

#[crux_test]
fn crux_test() -> u8 {
    let x: Cow<[u8]> = Cow::Borrowed(b"foo");
    let y: Cow<[u8]> = Cow::Owned(b"bar".to_vec());
    x[0] + y[0]
}

pub fn main() {
    println!("{:?}", crux_test());
}
