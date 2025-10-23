#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let arr = [10, 20, 30, 40];
    unsafe {
        let p = &arr[2] as *const i32;
        let p2 = intrinsics::arith_offset(p, -2);
        *p2 // expect 10
    }
}

pub fn main() { println!("{:?}", crux_test()); }
