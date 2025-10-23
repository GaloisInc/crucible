#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut arr = [7, 8, 9];
    unsafe {
        let p = &mut arr[1] as *mut i32;
        let p_next = intrinsics::offset(p, 1isize);
        *p_next // should be 9
    }
}

pub fn main() { println!("{:?}", crux_test()); }
