use std::ops::IndexMut;

fn g(ys: &mut [u8]) -> &mut [u8] {
    ys[1] = 7;
    ys
}

fn f(x: u8) -> u8 {
    let mut xs = [x,1,2,3, 4];
    let ys = g (&mut xs[1..4]);
    ys[1]
}

const ARG: u8 = 42;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
