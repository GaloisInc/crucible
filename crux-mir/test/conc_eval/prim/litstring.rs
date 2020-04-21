#![cfg_attr(not(with_main), no_std)]
fn f(x: usize) -> bool {
    let s = "hello";
    s.len() > x
}

const ARG: usize = 2;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG))
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> bool { f(ARG) }
