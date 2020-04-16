#![feature(custom_attribute)]
#![feature(ptr_offset_from)]
use std::ptr;

#[crux_test]
fn crux_test() -> isize {
    let a = [1, 2, 3];
    unsafe { (&a[0] as *const i32).offset_from(&a[2] as *const _) }
}

pub fn main() {
    println!("{:?}", crux_test());
}
