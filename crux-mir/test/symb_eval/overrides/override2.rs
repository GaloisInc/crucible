#![no_std]
#[macro_use] extern crate crucible;
use crucible::*;

#[allow(unused_variables)]
pub fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    let foo = crucible_i8("foo");
    crucible_assert!(foo + 1 == foo);
    0
}

pub static ARG: u8 = 1;
