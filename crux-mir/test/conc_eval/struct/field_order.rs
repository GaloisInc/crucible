#![cfg_attr(not(with_main), no_std)]

pub struct S {
    x: u8,
    y: u16,
}

#[cfg_attr(crux, crux::test)]
pub fn f() {
    // If the field ordering used in `buildStruct` is wrong, then this will fail due to type
    // mismatches between BVRepr 8 and BVRepr 16.
    let s = S { x: 1, y: 2 };
    assert!(s.x == 1);
    assert!(s.y == 2);
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
