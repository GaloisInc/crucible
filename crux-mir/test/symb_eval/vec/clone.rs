// Guard the call to clone() behind an intermediate function to reduce the
// likelihood that rustc optimizes away the call to clone().
#[inline(never)]
fn my_clone<T: Clone>(x: &T) -> T {
    x.clone()
}

#[crux::test]
pub fn f() {
    let v = vec![1, 2, 3];
    let w = my_clone(&v);
    assert!(v == w);
}
