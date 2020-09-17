extern crate crucible;
use crucible::array::Array;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut arr1 = [1];
    let mut arr2 = [2, 2];

    let c = bool::symbolic("c");
    let s = if c { &mut arr2 as &mut [_] } else { &mut arr1 as &mut [_] };
    let i = if c { 1 } else { 0 };
    s[i] = 0;
    crucible_assert!(arr1[0] == 0 || arr2[1] == 0);
    arr1[0] + arr2[0] + arr2[1]
}

pub fn main() {
    println!("{:?}", crux_test());
}
