#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
#[cfg_attr(with_main, derive(Debug))]
struct S {
    x: u8,
    y: i32,
}

fn f(_: ()) -> u8 {
    let s = S { x: 42, y: 120 };
    s.x
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u8 { f(ARG) }
