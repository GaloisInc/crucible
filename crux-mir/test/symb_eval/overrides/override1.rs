#![no_std]
extern crate crucible;
use crucible::*;

pub fn f(x: u8) -> u8 {
    // This call should be replaced by the test override
    x + one()
}

pub static ARG: u8 = 1;
