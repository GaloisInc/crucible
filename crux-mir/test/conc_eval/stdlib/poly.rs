#![cfg_attr(not(with_main), no_std)]
fn h<T>(x :T) -> T { x }

fn g<T>(x :T) -> T { h (x) }

fn f (x : u32) -> u32 {
    1 + g (x)
}

const ARG :u32 = 0;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
