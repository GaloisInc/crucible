#![cfg_attr(not(with_main), no_std)]
// This tests using polymorphic functions and parameterized data
// relies on Option type from std library

pub fn g<T>(y : Option<T>) -> Option<T> {
    y
}

fn f (x : u32) -> u32 {
    let z : Option<u32> = Some(x);
    match g(z) {
        Some (y) => return y,
        None => return 0
    }
}

const ARG : u32 = 27;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u32 { f(ARG) }
