#![cfg_attr(not(with_main), no_std)]
fn g(xs: &[u8]) -> u8 {
    xs[0]
}

fn f(x: u8) -> u8 {
    let xs = [x; 4];
    g(&xs)
}

const ARG: u8 = 42;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u8 { f(ARG) }
