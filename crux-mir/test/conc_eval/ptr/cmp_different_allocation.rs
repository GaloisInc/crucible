// FAIL: comparing pointers derived from different allocations

// This is a variant of the `cmp_same_allocation.rs` test case that tries to
// compare two raw pointers that are not derived from the same allocation. This
// is possible in native Rust, as comparing raw pointers amounts to comparing
// their memory addresses, but this is not yet possible in crucible-mir, as its
// model of raw pointers is too high-level to represent addresses.

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let a: [u32; 3] = [1, 2, 3];
    let a_s: &[u32] = &a;
    let a_p: *const u32 = a_s.as_ptr();

    let b: [u32; 3] = [4, 5, 6];
    let b_s: &[u32] = &b;
    let b_p: *const u32 = b_s.as_ptr();

    assert!(b_p < a_p || b_p >= a_p);
}

pub fn main() {
    println!("{:?}", crux_test());
}
