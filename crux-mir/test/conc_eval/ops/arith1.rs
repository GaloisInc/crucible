#![cfg_attr(not(with_main), no_std)]
extern crate core;
use core::ops::Add;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Digit(u8);

impl Add for Digit {
    type Output = Digit;
    fn add(self, other: Digit) -> Digit {
        Digit((self.0 + other.0) % 10)
    }
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let d0 = Digit(0);
    let d1 = Digit(1);
    let d9 = Digit(9);
    assert!(d0 + d1 == d1);
    assert!(d0 + d9 == d9);
    assert!(d1 + d9 == d0);
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
