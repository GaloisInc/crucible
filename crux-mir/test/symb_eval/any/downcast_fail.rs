#![feature(crucible_intrinsics)]

extern crate crucible;
use crucible::any::Any;

#[crux::test]
fn crux_test() -> i32 {
    let x: () = ();
    let a = Any::new(x);
    unsafe { a.downcast::<i32>() }
}

pub fn main() {
    println!("{:?}", crux_test());
}
