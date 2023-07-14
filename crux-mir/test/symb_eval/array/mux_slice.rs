extern crate crucible;
use crucible::array::Array;
use crucible::*;

#[crux::test]
fn crux_test() -> i32 {
    let mut arr1 = Array::<i32>::zeroed();
    let mut arr2 = Array::<i32>::zeroed();
    for i in 0..10 {
        arr1 = arr1.update(i, i as i32);
        arr2 = arr2.update(i, 9 - i as i32);
    }

    let s: &[i32] = if bool::symbolic("cond") {
        arr1.as_slice(0, 10)
    } else {
        arr2.as_slice(0, 10)
    };
    crucible_assert!(s.iter().cloned().sum::<i32>() == 45);
    s[5]
}

pub fn main() {
    println!("{:?}", crux_test());
}
