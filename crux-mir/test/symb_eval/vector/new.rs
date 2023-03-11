#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let v = Vector::<u8>::new();
    crucible_assert!(v.len() == 0);
}
