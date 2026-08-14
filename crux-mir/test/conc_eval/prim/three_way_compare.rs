// A regression test for https://github.com/GaloisInc/crucible/issues/1765. The
// implementations of `partial_cmp` and `cmp` for the char type and primitive
// integer types are implemented in terms of the `three_way_compare` intrinsic.
#![feature(core_intrinsics)]

use std::cmp::Ordering;
use std::intrinsics::three_way_compare;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    assert!(three_way_compare(0u8, 1u8) == Ordering::Less);
    assert!(three_way_compare(0u8, 0u8) == Ordering::Equal);
    assert!(three_way_compare(1u8, 0u8) == Ordering::Greater);

    assert!(three_way_compare(-1i8,  1i8) == Ordering::Less);
    assert!(three_way_compare(-1i8, -1i8) == Ordering::Equal);
    assert!(three_way_compare( 1i8, -1i8) == Ordering::Greater);

    assert!(three_way_compare('a', 'b') == Ordering::Less);
    assert!(three_way_compare('a', 'a') == Ordering::Equal);
    assert!(three_way_compare('b', 'a') == Ordering::Greater);
}

pub fn main() {
    println!("{:?}", crux_test())
}
