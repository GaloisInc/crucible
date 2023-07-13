#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[crux::test]
pub fn f() {
    let v = Vector::<u8>::copy_from_slice(&[1, 2, 3, 4]);
    crucible_assert!(v.len() == 4);
    crucible_assert!(v.as_slice()[0] == 1);
    crucible_assert!(v.as_slice()[1] == 2);
    crucible_assert!(v.as_slice()[2] == 3);
    crucible_assert!(v.as_slice()[3] == 4);
}
