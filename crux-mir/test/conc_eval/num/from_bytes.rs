#![cfg_attr(not(with_main), no_std)]

#[crux_test]
pub fn f() {
    assert!(u16::from_be_bytes([0x12, 0x34]) == 0x1234);
    assert!(u16::from_le_bytes([0x12, 0x34]) == 0x3412);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
