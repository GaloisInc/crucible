#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let mut arr = [1, 2, 3];
    unsafe {
        let p = &mut arr[2] as *mut i32;
        let p2 = intrinsics::arith_offset(p, 1); // one-past-the-end
        // Only check pointer arithmetic, do not deref
    }
}

pub fn main() { println!("{:?}", crux_test()); }
