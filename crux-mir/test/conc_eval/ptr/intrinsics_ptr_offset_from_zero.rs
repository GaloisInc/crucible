#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> isize {
    let arr = [10u8, 20, 30, 40];
    unsafe {
        let p = &arr[2] as *const u8;
        intrinsics::ptr_offset_from(p, p) // expect 0
    }
}

pub fn main() { println!("{:?}", crux_test()); }
