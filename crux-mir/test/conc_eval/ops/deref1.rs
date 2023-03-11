#![cfg_attr(not(with_main), no_std)]
extern crate core;
use core::ops::Deref;

struct S;

impl Deref for S {
    type Target = S;
    fn deref(&self) -> &S {
        static THE_S: S = S;
        &THE_S
    }
}

const ARG: i32 = 1;
fn f(arg: i32) {
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> () { f(ARG) }
