#![cfg_attr(not(with_main), no_std)]
fn f (y : u32) -> u32 {
    let mut x = y;
    for k in 0 .. 10 {
        x = x + k;
    }

    return x;
}


const ARG :u32 = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
