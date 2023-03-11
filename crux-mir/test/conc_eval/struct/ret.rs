#![cfg_attr(not(with_main), no_std)]
#[cfg_attr(with_main, derive(Debug))]
struct S {
    x: u8,
    y: i32,
}

fn f(_: ()) -> S {
    S { x: 42, y: 120 }
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> S { f(ARG) }
