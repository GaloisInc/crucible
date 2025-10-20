#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> isize {
    let arr = [10u8, 20, 30, 40];
    unsafe {
        let p1 = &arr[0] as *const u8;
        let p2 = unsafe { p1.add(4) }; // one past the end
        intrinsics::ptr_offset_from(p2, p1) // expect 4
    }
}

pub fn main() { println!("{:?}", crux_test()); }
