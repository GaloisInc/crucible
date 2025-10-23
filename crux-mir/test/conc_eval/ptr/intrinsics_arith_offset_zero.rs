#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let arr = [100, 200, 300];
    unsafe {
        let p = &arr[1] as *const i32;
        let p2 = intrinsics::arith_offset(p, 0);
        *p2 // expect 200
    }
}

pub fn main() { println!("{:?}", crux_test()); }
