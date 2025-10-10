// A regression test for #1564. This ensures that `crucible-mir` can correctly
// deem two pointers to be equal even when their types differ, which is
// something that can occur when pointer type casting is involved.

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
