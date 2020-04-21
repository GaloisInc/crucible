#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut v = Vector::<u8>::new().push(12).push(34);
    crucible_assert!(v.len() == 2);
    let s = v.as_mut_slice();
    crucible_assert!(s.len() == 2);
    crucible_assert!(s[0] == 12);
    crucible_assert!(s[1] == 34);
}
