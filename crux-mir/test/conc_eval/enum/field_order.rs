#![cfg_attr(not(with_main), no_std)]
#![feature(custom_attribute)]

pub enum E {
    A(u8, u16),
}

#[crux_test]
pub fn f() {
    // If the field ordering used in `buildEnum` is wrong, then this will fail due to type
    // mismatches between BVRepr 8 and BVRepr 16.
    match E::A(1, 2) {
        E::A(x, y) => assert!(x == 1 && y == 2),
    }
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
