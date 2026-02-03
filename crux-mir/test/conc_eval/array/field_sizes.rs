//! A regression test for a bug introduced during #1704, in which `crucible-mir`
//! would incorrectly compute the size of `S` as the size of its last field (See
//! https://github.com/GaloisInc/crucible/pull/1704#discussion_r2748562562).
//! Since the values in `arr` are written to (and read from) aggregates at an
//! offset of index * size, all array writes would go to offset 0, and all reads
//! would be of offset 0. The last thing written to offset 0 is the last element
//! of the array, so `crux_test()` would incorrectly return 9.

struct S(i32, ());

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let arr = [S(1, ()), S(2, ()), S(3, ())];
    arr[0].0 + arr[1].0 + arr[2].0 // expect 6
}

pub fn main() {
    println!("{:?}", crux_test());
}
