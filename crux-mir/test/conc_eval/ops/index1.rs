#![cfg_attr(not(with_main), no_std)]
extern crate core;
use core::ops::Index;

struct S;

impl Index<u32> for S {
    type Output = S;
    fn index(&self, idx: u32) -> &S {
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
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> () { f(ARG) }
