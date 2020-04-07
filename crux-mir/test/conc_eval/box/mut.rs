#![cfg_attr(not(with_main), no_std)]

#[cfg(not(with_main))] extern crate std;
#[cfg(not(with_main))] use std::boxed::Box;

#[crux_test]
pub fn f() {
    let mut b = Box::new(123_i32);
    assert!(*b == 123);
    *b = 456;
    assert!(*b == 456);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
