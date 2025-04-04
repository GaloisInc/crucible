#![cfg_attr(not(with_main), no_std)]

#[cfg(not(with_main))] extern crate std;
#[cfg(not(with_main))] use std::boxed::Box;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let mut b = Box::new(123_i32);
    let r = &mut *b;
    assert!(*r == 123);
    *r = 456;
    assert!(*r == 456);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
