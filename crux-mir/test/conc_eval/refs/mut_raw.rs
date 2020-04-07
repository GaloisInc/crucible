#![cfg_attr(not(with_main), no_std)]

unsafe fn g(ptr: *mut i32) -> i32 {
    *ptr
}

pub fn f(x: i32) -> i32 {
    let mut x = 123;
    unsafe { g(&mut x as *mut i32) }
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { f(ARG) }
