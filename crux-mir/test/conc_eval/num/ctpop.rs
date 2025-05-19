#![cfg_attr(not(with_main), no_std)]
#![feature(core_intrinsics)]

extern crate core;
use core::intrinsics::ctpop;

#[cfg_attr(crux, crux::test)]
fn ctpop_test() {
    // Test at each of u{16,32,64} to ensure that zero-extension, identity, and
    // truncation operations (respectively) work as expected.

    assert_eq!(ctpop(0_u16), 0_u32);
    assert_eq!(ctpop(0_u32), 0_u32);
    assert_eq!(ctpop(0_u64), 0_u32);

    assert_eq!(ctpop(1_u16), 1_u32);
    assert_eq!(ctpop(1_u32), 1_u32);
    assert_eq!(ctpop(1_u64), 1_u32);

    assert_eq!(ctpop(5_u16), 2_u32);
    assert_eq!(ctpop(5_u32), 2_u32);
    assert_eq!(ctpop(5_u64), 2_u32);

    assert_eq!(ctpop(u16::MAX), u16::BITS);
    assert_eq!(ctpop(u32::MAX), u32::BITS);
    assert_eq!(ctpop(u64::MAX), u64::BITS);
}

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", ctpop_test());
}
