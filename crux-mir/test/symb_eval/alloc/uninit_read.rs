extern crate crucible;
use crucible::*;
use crucible::alloc::allocate;

#[crux::test]
fn crux_test() -> i32 {
    unsafe {
        let ptr = allocate::<i32>(10);
        *ptr.offset(3)
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}

