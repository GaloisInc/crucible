#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let arr = [0u8; 3];
    unsafe {
        let p = &arr[0] as *const u8;
        let _out_of_bounds = intrinsics::offset(p, 5isize); // No dereference so this should pass
    }
}

pub fn main() { println!("{:?}", crux_test()); }
