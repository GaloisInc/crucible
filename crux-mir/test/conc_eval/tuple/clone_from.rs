// FAIL: clone_from shims are not yet implemented

#[crux_test]
pub fn f() {
    let x = (1, 2);
    let mut y = (0, 0);
    y.clone_from(&x);
    assert!(x == y);
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
