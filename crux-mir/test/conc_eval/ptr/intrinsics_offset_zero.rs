#![feature(core_intrinsics)]
use std::intrinsics;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = 42;
    unsafe {
        let p = &x as *const i32;
        let p0 = intrinsics::offset(p, 0isize);
        *p0 // should be 42
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
