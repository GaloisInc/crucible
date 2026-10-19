#![feature(crucible_intrinsics)]

extern crate crucible;
use crucible::alloc::{allocate, reallocate};

#[crux::test]
fn crux_test() -> [u32; 4] {
    unsafe {
        let p2: *mut u32 = allocate::<u32>(2);
        let p4: *mut u32 = reallocate(p2, 4);

        for o in 0..4 {
            p4.add(o).write(o as u32);
        }
        std::ptr::read(p4 as *mut [u32; 4])
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
