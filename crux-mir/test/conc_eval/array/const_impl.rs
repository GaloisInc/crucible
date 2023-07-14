#![cfg_attr(not(with_main), no_std)]
// Tests calls to methods defined in const impls.

pub fn f(x: i32) -> usize {
    let arr: [i32; 5] = [x; 5];
    arr.as_ref().len()
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> usize { f(ARG) }
