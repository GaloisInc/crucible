extern crate crucible;
use crucible::*;
use crucible::alloc::allocate;

#[crux::test]
fn crux_test() {
    unsafe {
        // Make sure the CustomOp succeeds in creating a pointer to the first element of an empty
        // allocation.
        let ptr = allocate::<i32>(0);
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}

