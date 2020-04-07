#![cfg_attr(not(with_main), no_std)]
pub fn f(x: i32) -> i32 {
    let x = 123;
    let rf: &i32 = &x;
    *rf
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { f(ARG) }
