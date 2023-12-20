#![cfg_attr(not(with_main), no_std)]
// Test iterator for 0-length vec

#[cfg(not(with_main))] extern crate std;
#[cfg(not(with_main))] use std::vec;

pub fn f(count: u32) -> u32 {
    let mut v1 = vec![];
    (0..count).for_each(|i| v1.push(i));
    let mut sum = 0;
    for i in v1 {
        sum += i;
    }
    sum
}

pub static ARG: u32 = 0;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u32 { f(ARG) }
