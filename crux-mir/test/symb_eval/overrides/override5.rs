#![no_std]
#[macro_use] extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    // This call should be replaced by the test override
    let foo = crucible_u64("foo");
    crucible_assume!(foo != 0);
    crucible_assert!(foo.wrapping_add(1) != 0);
}
