// A regression test for
// https://github.com/GaloisInc/crucible/issues/1140
#![cfg_attr(not(with_main), no_std)]

#[repr(transparent)]
pub enum E {
    MkE(u32),
}

pub fn f() -> u32 {
    let x = E::MkE(42);
    match x {
        E::MkE(y) => y,
    }
}

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f());
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u32 { f() }
