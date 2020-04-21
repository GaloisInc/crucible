#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let v = Vector::<u8>::copy_from_slice(&[1, 2, 3, 4]);
    let (v1, v2) = v.split_at(2);
    crucible_assert!(v1.len() == 2);
    crucible_assert!(v1.as_slice()[0] == 1);
    crucible_assert!(v1.as_slice()[1] == 2);
    crucible_assert!(v2.len() == 2);
    crucible_assert!(v2.as_slice()[0] == 3);
    crucible_assert!(v2.as_slice()[1] == 4);
}
