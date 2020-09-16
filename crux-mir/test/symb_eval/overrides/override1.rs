#![no_std]
extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
pub fn f() -> u8 {
    let x: u8 = 1;
    // This call should be replaced by the test override
    x + one()
}
