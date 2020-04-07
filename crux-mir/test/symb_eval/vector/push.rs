#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[crux_test]
pub fn f() {
    let v = Vector::<u8>::new();
    crucible_assert!(v.len() == 0);
    let v = v.push(12);
    crucible_assert!(v.len() == 1);
    let v = v.push(34);
    crucible_assert!(v.len() == 2);
}
