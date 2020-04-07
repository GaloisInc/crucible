#![cfg_attr(not(with_main), no_std)]
#![feature(slice_index_methods)]
extern crate core;

use core::slice::SliceIndex;
use core::ops::Range;

fn f(x: u8) -> u8 {
    let xs = [x; 4];
    let ys = &xs[1..];
    // usize -> u8 cast is unsupported, so we can't simply return `len as u8`.
    assert!(ys.len() == 3);
    1
}

const ARG: u8 = 42;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u8 { f(ARG) }
