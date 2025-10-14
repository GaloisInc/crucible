#![feature(core_intrinsics)]
#![feature(ptr_offset_from_unsigned)]
use std::intrinsics::ptr_offset_from_unsigned;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    let a = [1, 2, 3];
    // This should return 2: &a[2] is 2 elements after &a[0]
    unsafe { ptr_offset_from_unsigned(&a[2] as *const i32, &a[0] as *const i32) }
}

pub fn main() {
    println!("{:?}", crux_test());
}
