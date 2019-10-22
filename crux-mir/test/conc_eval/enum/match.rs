#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
enum E {
    A(u8),
    B(i32),
}

fn f(_: ()) -> u8 {
    let x = E::A(42);
    match x {
        E::A(n) => n,
        E::B(n) => 0,
    }
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u8 { f(ARG) }
