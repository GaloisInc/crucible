#![feature(custom_attribute)]
extern crate crucible;
use crucible::*;
use crucible::alloc::allocate;

#[crux_test]
fn crux_test() -> i32 {
    unsafe {
        let ptr = allocate::<i32>(10);
        for i in 0..10 {
            *ptr.offset(i) = i as i32;
        }
        *ptr.offset(12)
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}

