#![cfg_attr(not(with_main), no_std)]

fn f(_x: u8) -> i32 {
    let mut xs : [i32; 3] = [0; 3];
    xs[1] = 1;
    xs[2] = 2;
    let mut y : i32 = 0;
    // Currently we require an explicit cast because the IntoIterator impls use const generics
    // (which crux-mir doesn't yet support).
    for x in (&xs as &[_]) {
        y += x;
    }
    y
}

const ARG: u8 = 42;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
