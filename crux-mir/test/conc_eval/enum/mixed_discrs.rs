#![cfg_attr(not(with_main), no_std)]
#![feature(core_intrinsics)]

extern crate core;
use core::intrinsics::discriminant_value;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum E {
    A = 10,
    B,
    C,
    D = 20,
}

#[cfg_attr(crux, crux_test)]
pub fn f() {
    unsafe {
        assert!(discriminant_value(&E::A) == 10);
        assert!(discriminant_value(&E::B) == 11);
        assert!(discriminant_value(&E::C) == 12);
        assert!(discriminant_value(&E::D) == 20);
    }
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
