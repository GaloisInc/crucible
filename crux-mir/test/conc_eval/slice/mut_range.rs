#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
fn g(xs: &mut [u16]) {
    xs[0] = xs[0] + 1;
    xs[1] = xs[1] + 1;
}

fn f(x: u16) -> u16 {
    let mut xs = [x; 4];
    let y = g(&mut xs[1..]);
    xs[1] + xs[2]
}

const ARG: u16 = 42;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u16 { f(ARG) }
