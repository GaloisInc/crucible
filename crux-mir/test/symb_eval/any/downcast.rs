#![feature(crucible_intrinsics)]

extern crate crucible;
use crucible::any::Any;

#[crux_test]
fn crux_test() -> i32 {
    let x: i32 = 1;
    let a = Any::new(x);
    unsafe { a.downcast::<i32>() }
}

pub fn main() {
    println!("{:?}", crux_test());
}
