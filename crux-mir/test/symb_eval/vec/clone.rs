
#[cfg_attr(crux, crux_test)]
pub fn f() {
    let v = vec![1, 2, 3];
    let w = v.clone();
    assert!(v == w);
}
