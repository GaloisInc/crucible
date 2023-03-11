#![cfg_attr(not(with_main), no_std)]
fn f(x: i64) -> i64 {
    x << 63u8
}

const ARG: i64 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i64 { f(ARG) }
