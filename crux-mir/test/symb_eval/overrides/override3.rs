#[macro_use] extern crate crucible;
use crucible::*;

#[allow(unused_variables)]
fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    let foo = crucible_i8("x");
    crucible_assert!(foo + 1 != foo);
    0
}

const ARG: u8 = 1;

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
