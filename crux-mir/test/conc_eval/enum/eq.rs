#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum E {
    A(u8), B, C,
}

pub fn f(x: i32) {
    assert!(E::B == E::B);
    assert!(E::A(1) != E::B);
    assert!(E::A(1) != E::A(0));
}


pub const ARG : i32 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() { f(ARG) }
