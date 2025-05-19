#![cfg_attr(not(with_main), no_std)]

fn f (y:i32) -> i32 {
    let z = 12;
    let w = 13;

    let g = |x:i32| x + y + z + w;

    g(1)

}

const ARG :i32 = 3;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
