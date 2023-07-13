#![no_std]
#[macro_use] extern crate crucible;
use crucible::*;

#[crux::test]
pub fn f() {
    // This call should be replaced by the test override
    let foo = crucible_i8("foo");
    crucible_assert!(foo.wrapping_add(1) == foo);
}
