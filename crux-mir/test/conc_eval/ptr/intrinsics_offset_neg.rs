#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let arr = [10, 20, 30];
    unsafe {
        let p = &arr[2] as *const i32;
        let p0 = intrinsics::offset(p, -2isize);
        *p0 // should be 10
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
