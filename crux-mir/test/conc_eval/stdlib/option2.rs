#![cfg_attr(not(with_main), no_std)]

pub enum Opt<T> {
    N,
    S(T),
}

use Opt::*;

fn g<T> (x : Opt<T>) -> T {
    match x {
        S(y) => y,
        N    => g(x),
    }
}


fn f (y : u32) -> u32 { 
    let x: Opt<u32> = S(0);
    return g(x);
}

const ARG: u32 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
