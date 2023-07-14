#![cfg_attr(not(with_main), no_std)]

extern crate core;
use core::convert::TryFrom;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let xs = [1, 2, 3, 4];
    let xs: &[u8] = &xs;

    assert!(<&[u8; 3] as TryFrom<_>>::try_from(xs).is_err());
    assert!(<&[u8; 5] as TryFrom<_>>::try_from(xs).is_err());
    let ys = <&[u8; 4] as TryFrom<_>>::try_from(xs).unwrap();
    assert!(ys == xs);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
