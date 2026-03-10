#![cfg_attr(not(with_main), no_std)]

/// Make sure that the unsupported SliceContains specializations are removed
#[cfg_attr(crux, crux::test)]
pub fn f() {
    let arr = &[0u8; 256];
    assert!(arr.contains(&0));
    let arr = &[0i8; 256];
    assert!(arr.contains(&0));
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
