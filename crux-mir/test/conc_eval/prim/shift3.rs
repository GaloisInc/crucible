#![cfg_attr(not(with_main), no_std)]
fn f(x: i64) -> i64 {
    x << 63i64
}

const ARG: i64 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
