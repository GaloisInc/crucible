#![no_std]
#[macro_use] extern crate crucible;
use crucible::vector::Vector;

#[crux::test]
pub fn f() {
    let mut v = Vector::<u8>::new().push(12).push(34);
    {
        let s = v.as_mut_slice();
        s[0] = 99;
    }
    {
        let s = v.as_slice();
        crucible_assert!(s[0] == 99);
        crucible_assert!(s[1] == 34);
    }
}
