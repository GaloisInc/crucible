extern crate crucible;
use crucible::alloc::{allocate, reallocate};

#[crux::test]
fn crux_test() {
    unsafe {
        let p8: *mut u32 = allocate::<u32>(8);
        let p8a: *mut u32 = p8.add(4);
        // The current implementation of `reallocate` only permits reallocation
        // if its parameter points to the beginning of a block of
        // previously-`allocate`d memory, so this attempt to reallocate starting
        // from the middle of the block should fail.
        let p4: *mut u32 = reallocate(p8a, 4);
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
