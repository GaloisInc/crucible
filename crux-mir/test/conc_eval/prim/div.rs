#![cfg_attr(not(with_main), no_std)]
fn f(x: u8) -> u8 {
    x / 2
}

const ARG: u8 = 9;

#[cfg(with_main)]
pub fn main() {
    println!("{}", println!("{:?}", f(ARG)))
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
