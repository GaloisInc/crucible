#![feature(custom_attribute)]
extern crate crucible;
use crucible::array::Array;
use crucible::*;

#[crux_test]
fn crux_test() -> i32 {
    let mut arr = Array::<i32>::zeroed();
    for i in 0..10 {
        arr = arr.update(i, i as i32);
    }
    crucible_assert!(arr.as_slice(0, 10).iter().cloned().sum::<i32>() == 45);
    crucible_assert!(arr.as_slice(0, 5).iter().cloned().sum::<i32>() == 10);
    crucible_assert!(arr.as_slice(5, 10).iter().cloned().sum::<i32>() == 45 - 10);
    arr.lookup(5)
}

pub fn main() {
    println!("{:?}", crux_test());
}
