#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> isize {
    let mut arr = [1, 2, 3, 4];
    unsafe {
        let p1 = &mut arr[1] as *mut i32;
        let p2 = &mut arr[3] as *mut i32;
        intrinsics::ptr_offset_from(p2, p1) // expect 2
    }
}

pub fn main() { println!("{:?}", crux_test()); }
