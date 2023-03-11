#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let v = Vector::<u8>::replicate(123, 4);
    crucible_assert!(v.len() == 4);
    for i in 0 .. 4 {
        crucible_assert!(v.as_slice()[i] == 123);
    }
}
