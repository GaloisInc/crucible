#![no_std]
#![feature(custom_attribute)]
#[macro_use] extern crate crucible;
use crucible::*;

#[crux_test]
pub fn f() {
    // This call should be replaced by the test override
    let foo = crucible_i8("foo");
    crucible_assert!(foo + 1 == foo);
}
