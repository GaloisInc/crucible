#![cfg_attr(not(with_main), no_std)]
fn f(x: u8) -> u8 {
    x << 1i32
}

const ARG: u8 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u8 { f(ARG) }
