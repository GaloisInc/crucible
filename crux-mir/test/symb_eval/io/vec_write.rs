#![no_std]
#![feature(custom_attribute)]
#[macro_use] extern crate crucible;
extern crate std;
use std::io::Write;
use std::vec::Vec;

#[crux_test]
pub fn f() {
    let mut buf = Vec::new();
    buf.write(&[1, 2, 3]);

    crucible_assert!(buf.len() == 3);
    crucible_assert!(buf[0] == 1);
    crucible_assert!(buf[1] == 2);
    crucible_assert!(buf[2] == 3);
}
