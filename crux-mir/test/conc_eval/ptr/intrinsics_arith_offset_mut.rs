#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut arr = [7, 8, 9, 10];
    unsafe {
        let p = &mut arr[0] as *mut i32;
        let p2 = intrinsics::arith_offset(p, 2);
        *p2 // expect 9
    }
}

pub fn main() { println!("{:?}", crux_test()); }

