#![cfg_attr(not(with_main), no_std)]

#[crux_test]
pub fn f() {
    let mut a = 123_i32;
    let mut b = &mut a;
    let c = &mut b;
    assert!(**c == 123);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
