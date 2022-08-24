
#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    assert_eq!( u8::swap_bytes(0x94_u8), 0x94_u8);
    assert_eq!(u32::swap_bytes(0xface9412_u32), 0x1294cefa_u32);
    assert_eq!(i32::swap_bytes(0x00000080_i32), -0x80000000_i32);
    i32::swap_bytes(0x00000080_i32)
}

pub fn main() {
    println!("{:?}", crux_test());
}
