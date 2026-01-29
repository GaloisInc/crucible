// FAIL: `ptr_offset_from` UB: byte offset not a multiple of `size_of::<T>`

#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> isize {
    let mut arr: [u8; 4] = [1, 2, 3, 4];
    unsafe {
        let p1 = &mut arr[1] as *mut u8 as *mut u16;
        let p2 = &mut arr[2] as *mut u8 as *mut u16;

        intrinsics::ptr_offset_from(p2, p1)
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
