#![cfg_attr(not(with_main), no_std)]
// parameter is mutable in Rust, so we must make a local variable on translation

fn h(x: &mut[u8; 4]) -> [u8; 4] {
    x[0] = 42;
    *x
}

fn f(x:u8) -> u8 {
    let mut y = [0;4];
    h(&mut y);
    y[0]
}

const ARG: u8 = 4;



#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u8 { f(ARG) }
