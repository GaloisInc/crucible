#![no_std]
#![feature(custom_attribute)]
extern crate crucible;
use crucible::*;

#[crux_test]
pub fn f() -> u8 {
    let x: u8 = 1;
    // This call should be replaced by the test override
    x + one()
}
