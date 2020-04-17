#![cfg_attr(not(with_main), feature(custom_attribute))]
#![cfg_attr(not(with_main), no_std)]
pub fn call_it<F: FnMut(i32) -> i32>(f: F) -> i32 {
    let mut f = f;
    f(1)
}

pub fn convert_it<F: Fn(i32) -> i32>(f: F) -> i32 {
    call_it(f)
}

pub fn f(x: i32) -> i32 {
    convert_it(|y| x + y)
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { f(ARG) }
