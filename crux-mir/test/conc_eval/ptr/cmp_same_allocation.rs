// A test exercising the subset of raw pointer comparisons that crucible-mir
// currently supports.

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let a: [u32; 3] = [1, 2, 3];
    let s: &[u32] = &a;
    let p: *const u32 = s.as_ptr();
    let q = unsafe { p.add(3) };

    // Comparing a pointer to itself
    assert!(!(p < p));
    assert!(p <= p);
    assert!(!(p > p));
    assert!(p >= p);

    assert!(!(q < q));
    assert!(q <= q);
    assert!(!(q > q));
    assert!(q >= q);

    // Comparing a pointer to another pointer derived from the same allocation
    assert!(p < q);
    assert!(p <= q);
    assert!(!(p > q));
    assert!(!(p >= q));
}

pub fn main() {
    println!("{:?}", crux_test());
}
