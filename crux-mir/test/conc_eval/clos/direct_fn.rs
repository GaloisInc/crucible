#![cfg_attr(not(with_main), no_std)]
pub fn call_it<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(1)
}

pub fn f(x: i32) -> i32 {
    call_it(|y| x + y)
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> i32 { f(ARG) }
