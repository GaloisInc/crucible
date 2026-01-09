extern crate crucible;
use crucible::*;
use crucible::array::Array;

#[crux::test]
fn crux_test() -> (i32, i32, i32) {
    let arr = Array::symbolic("arr");
    let s = arr.as_slice(0, 3);
    for i in 0..3 {
        crucible_assume!(0 < s[i] && s[i] <= 10);
    }
    for i in 0..2 {
        crucible_assume!(s[i + 1] > s[i]);
    }
    crucible_assume!(s[0] + s[1] + s[2] == 6);

    // We can't concretize `s` directly because `concretize` will attempt to
    // concretize the entire backing allocation, and allocations backing
    // symbolic arrays (`Array`s) are modeled to have infinite size.
    let s0 = concretize(s[0]);
    let s1 = concretize(s[1]);
    let s2 = concretize(s[2]);
    (s0, s1, s2)
}

pub fn main() {
    println!("{:?}", crux_test());
}

