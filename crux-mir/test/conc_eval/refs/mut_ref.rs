#![cfg_attr(not(with_main), no_std)]
pub fn f(x: i32) -> i32 {
    let mut x = x;
    let rf: &mut i32 = &mut x;
    *rf
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] pub fn main() { f(ARG); }
