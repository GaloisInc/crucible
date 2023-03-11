#![cfg_attr(not(with_main), no_std)]
fn f(x: bool) -> bool {
    x ^ true
}

const ARG: bool = true;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG))
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> bool { f(ARG) }
