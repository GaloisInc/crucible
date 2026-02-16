#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (isize, isize, isize, isize) {
    let mut arr: [u64; 4] = [1, 2, 3, 4];
    unsafe {
        let e1 = &mut arr[1] as *mut u64;
        let e3 = &mut arr[3] as *mut u64;

        let o64 = intrinsics::ptr_offset_from(e3, e1);
        let o32 = intrinsics::ptr_offset_from(e3 as *mut u32, e1 as *mut u32);
        let o16 = intrinsics::ptr_offset_from(e3 as *mut u16, e1 as *mut u16);
        let o8 = intrinsics::ptr_offset_from(e3 as *mut u8, e1 as *mut u8);

        assert_eq!(o64, 2);
        assert_eq!(o32, 4);
        assert_eq!(o16, 8);
        assert_eq!(o8, 16);

        (o64, o32, o16, o8)
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
