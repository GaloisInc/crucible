#![feature(custom_attribute)]
use std::ptr;

#[crux_test]
fn crux_test() -> (i32, i32) {
    let a = [1, 2];
    let slice_ptr = &a as *const [i32];
    let ptr = slice_ptr as *const i32;
    unsafe { (*ptr, *ptr.offset(1)) }
}

pub fn main() {
    println!("{:?}", crux_test());
}
