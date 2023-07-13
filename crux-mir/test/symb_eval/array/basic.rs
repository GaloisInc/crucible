extern crate crucible;
use crucible::array::Array;

#[crux::test]
fn crux_test() -> i32 {
    let arr = Array::<i32>::zeroed();
    let arr = arr.update(0, 0);
    let arr = arr.update(1, 1);
    let arr = arr.update(2, 2);
    arr.lookup(0) + arr.lookup(1) + arr.lookup(2) + arr.lookup(99)
}

pub fn main() {
    println!("{:?}", crux_test());
}
