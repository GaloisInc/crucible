extern crate crucible;
use crucible::array::Array;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let arr1 = [1];
    let arr2 = [2, 2];

    let c = bool::symbolic("c");
    let s = if c { &arr2 as &[_] } else { &arr1 as &[_] };
    let i = if c { 1 } else { 0 };
    crucible_assert!(s[i] == 1 || s[i] == 2);
    s[i]
}

pub fn main() {
    println!("{:?}", crux_test());
}
