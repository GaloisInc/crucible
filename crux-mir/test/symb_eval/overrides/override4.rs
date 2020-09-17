#![no_std]
#[macro_use] extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
pub fn f() {
    // This call should be replaced by the test override
    let foo = crucible_i8("x");
    crucible_assume!(foo == 4);
    crucible_assert!(foo + 1 == 5);
}
