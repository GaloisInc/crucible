#![cfg_attr(not(with_main), no_std)]
fn h<T>(x :T) -> T { x }

fn f (x : u32) -> u32 {
    h (|y| y + 1)  (x)
}

const ARG :u32 = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
