#![cfg_attr(not(with_main), no_std)]
fn f(x: usize) -> bool {
    let s = b"hello";
    s.len() > x
}

const ARG: usize = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG))
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
