#![cfg_attr(not(with_main), no_std)]

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum E {
    A(u8), B, C,
}

pub fn f(x: i32) {
    let eb_eq = E::B == E::B;
    assert!(eb_eq);
    assert!(E::A(1) != E::B);
    assert!(E::A(1) != E::A(0));
}


pub const ARG : i32 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() { f(ARG) }
