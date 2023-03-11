#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let v = Vector::<u8>::new().push(12).push(34);
    crucible_assert!(v.len() == 2);
    let (v, x) = v.pop();
    crucible_assert!(v.len() == 1);
    crucible_assert!(x == Some(34));
    let (v, x) = v.pop();
    crucible_assert!(v.len() == 0);
    crucible_assert!(x == Some(12));
    let (v, x) = v.pop();
    crucible_assert!(v.len() == 0);
    crucible_assert!(x == None);
}
