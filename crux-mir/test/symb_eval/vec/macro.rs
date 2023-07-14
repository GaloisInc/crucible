
#[crux::test]
pub fn f() {
    let v = vec![1, 2, 3];
    assert!(v.len() == 3);
    assert!(v[0] == 1);
    assert!(v[1] == 2);
    assert!(v[2] == 3);
}
