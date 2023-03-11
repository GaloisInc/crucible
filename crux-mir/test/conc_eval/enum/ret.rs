#![cfg_attr(not(with_main), no_std)]
#[cfg_attr(with_main, derive(Debug))]
enum E {
    A(u8),
    B { x: i32 },
    C,
}

fn f(_: ()) -> (E, E, E) {
    (E::A(42), E::B { x: 42 }, E::C)
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> (E, E, E) { f(ARG) }
