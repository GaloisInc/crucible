#![cfg_attr(not(with_main), no_std)]

unsafe fn g(ptr: *const i32) -> i32 {
    *ptr
}

pub fn f(x: i32) -> i32 {
    let x = 123;
    unsafe { g(&x as *const i32) }
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
