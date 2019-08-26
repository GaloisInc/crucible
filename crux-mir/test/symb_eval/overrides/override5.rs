#![no_std]
#[macro_use] extern crate crucible;
use crucible::*;

pub fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    let foo = crucible_u64("foo");
    crucible_assume!(foo != 0);
    crucible_assert!(foo + 1 != 0);
    0
}

pub static ARG: u8 = 1;
