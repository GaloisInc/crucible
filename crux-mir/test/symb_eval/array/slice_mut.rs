extern crate crucible;
use crucible::array::Array;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut arr = Array::<i32>::zeroed();
    let xs = arr.as_mut_slice(0, 10);
    for i in 0..10 {
        xs[i] = i as i32;
    }
    for i in 0..10 {
        crucible_assert!(arr.lookup(i) == i as i32);
    }
    arr.lookup(5)
}

pub fn main() {
    println!("{:?}", crux_test());
}
