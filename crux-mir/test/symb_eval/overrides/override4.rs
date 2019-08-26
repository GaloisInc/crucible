#![no_std]
#[macro_use] extern crate crucible;
use crucible::*;

pub fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    let foo = crucible_i8("x");
    crucible_assume!(foo == 4);
    crucible_assert!(foo + 1 == 5);
    0
}

pub static ARG: u8 = 1;
