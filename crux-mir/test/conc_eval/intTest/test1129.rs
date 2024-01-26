//! Regression test for missing override for the `rotate_left` intrinsic

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let n: u32 = 0x10000b3u32;
    let expected = 0xb301;
    let actual = n.rotate_left(8);
    assert!(expected == actual);
    actual
}

pub fn main() {
    println!("{:?}", crux_test());
}
