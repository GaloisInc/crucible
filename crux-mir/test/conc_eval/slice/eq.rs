#![cfg_attr(not(with_main), no_std)]
#![feature(custom_attribute)]

#[crux_test]
pub fn f() {
    let arr = [1, 2, 3];
    let xs = &arr as &[_];
    let ys = &arr as &[_];
    assert!(xs == ys);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
