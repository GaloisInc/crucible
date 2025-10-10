// A regression test for #1564. This ensures that `crucible-mir` can correctly
// deem two pointers to be equal even when their types differ, which is
// something that can occur when pointer type casting is involved. Moreover,
// this tests that crucible-mir can correctly check for pointer equality when
// both pointers have an AgElem_RefPath in their path.
//
// Note that this test case implicitly relies on unspecified details of how the
// `Rust` representation lays out tuple types. More specifically, given `p :
// *const (A, B)`, it relies on the fact that `p` will have the same memory
// address as `&(*p).0`. This happens to be the case in this example, but is
// not guaranteed by anything stated in the Rust Reference (see
// https://doc.rust-lang.org/1.86.0/reference/type-layout.html#r-layout.repr.rust).
// If Rust ever changes this in the future, we will need to update this test
// case accordingly.

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    let x: (i32, i32) = (0, 1);
    let p0 = &x as *const (i32, i32);
    let q0: *const (u8, u8) = p0.cast();
    let p1: &i32 = unsafe { &(*p0).0 };
    let q1: &u8  = unsafe { &(*q0).0 };
    let p2 = p1 as *const i32;
    let q2 = q1 as *const u8;
    assert!(p2 == q2.cast());
}

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", crux_test());
}
