#![no_std]
#![feature(custom_attribute)]
#[macro_use] extern crate crucible;
use crucible::*;

#[crux_test]
pub fn f() {
    // This call should be replaced by the test override
    let foo = crucible_u64("foo");
    crucible_assume!(foo != 0);
    crucible_assert!(foo.wrapping_add(1) != 0);
}
