// FAIL: not mutating array

use std::ops::IndexMut;

fn g(ys: &mut [u8]) -> &mut [u8] {
    ys[0] = 2;
    ys
}

fn f(x: u8) -> u8 {
    let mut xs = [x; 4];
    let ys = g (&mut xs[2..3]);
    ys[0]
}

const ARG: u8 = 42;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
