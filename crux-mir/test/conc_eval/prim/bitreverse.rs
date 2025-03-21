#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u32 {
    let x: u32 = 0x12345678;
    let y: u32 = x.reverse_bits();
    assert_eq!(y, 0x1e6a2c48);
    assert_eq!(y.reverse_bits(), x);
    y
}

pub fn main() {
    println!("{:?}", crux_test());
}
