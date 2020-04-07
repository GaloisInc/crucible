#![feature(crux)]

#[crux_test]
pub fn f() {
    let v = vec![1, 2, 3];
    let mut it = v.into_iter();
    assert!(it.next() == Some(1));
    assert!(it.next() == Some(2));
    assert!(it.next() == Some(3));
    assert!(it.next() == None);
}
