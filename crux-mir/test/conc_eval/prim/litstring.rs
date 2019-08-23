#![cfg_attr(not(with_main), no_std)]
fn f(x: usize) -> bool {
    let s = "hello";
    s.len() > x
}

const ARG: usize = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{}", println!("{:?}", f(ARG)))
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
