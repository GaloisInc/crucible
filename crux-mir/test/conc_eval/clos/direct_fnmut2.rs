#![cfg_attr(not(with_main), no_std)]
pub fn call_it<F: FnMut(i32) -> i32>(f: F) -> i32 {
    let mut f = f;
    f(1)
}

pub fn f(x: i32) -> i32 {
    let mut z = 0;
    let a = call_it(|y| { z += 1; x + y + z });
    let b = call_it(|y| { z += 1; x + y + z });
    a + b
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { f(ARG) }
