#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[crux_test]
pub fn f() {
    let v1 = Vector::<u8>::new().push(1).push(2);
    let v2 = Vector::<u8>::new().push(3).push(4);
    let v = v1.concat(v2);
    crucible_assert!(v.len() == 4);
    crucible_assert!(v.as_slice()[0] == 1);
    crucible_assert!(v.as_slice()[1] == 2);
    crucible_assert!(v.as_slice()[2] == 3);
    crucible_assert!(v.as_slice()[3] == 4);
}
