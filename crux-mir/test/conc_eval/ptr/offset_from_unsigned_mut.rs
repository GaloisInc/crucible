#![feature(core_intrinsics)]
use std::intrinsics::ptr_offset_from_unsigned;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    let a = [1, 2, 3];
    let start = &a[0] as *const i32;
    let past_end = unsafe { start.add(3) }; // points just past end of array
    unsafe { ptr_offset_from_unsigned(past_end, start) } // should be 3
}

pub fn main() {
    println!("{:?}", crux_test());
}
