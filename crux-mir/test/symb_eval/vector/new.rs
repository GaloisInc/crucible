#![no_std]
#![feature(custom_attribute)]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[crux_test]
pub fn f() {
    let v = Vector::<u8>::new();
    crucible_assert!(v.len() == 0);
}
