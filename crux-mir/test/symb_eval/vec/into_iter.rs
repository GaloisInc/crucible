#![feature(custom_attribute)]

#[crux_test]
pub fn f() {
    let v = vec![1, 2, 3];
    let mut sum = 0;
    for x in v.into_iter() {
        // Easy way to check we're getting elements in the right order.
        assert!(sum < x * x);
        sum += x;
    }
    assert!(sum == 6);
}
