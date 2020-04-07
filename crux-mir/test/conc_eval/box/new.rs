#![cfg_attr(not(with_main), no_std)]

#[cfg(not(with_main))] extern crate std;
#[cfg(not(with_main))] use std::boxed::Box;

#[crux_test]
pub fn f() {
    let b = Box::new(123_i32);
    assert!(*b == 123);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
