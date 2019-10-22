#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
extern crate core;
use core::ops::IndexMut;

fn g(ys: &mut [u8]) -> &mut [u8] {
    ys[1] = 7;
    ys
}

fn f(x: u8) -> u8 {
    let mut xs = [x,1,2,3, 4];
    let ys = g (&mut xs[1..4]);
    ys[1]
}

const ARG: u8 = 42;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u8 { f(ARG) }
