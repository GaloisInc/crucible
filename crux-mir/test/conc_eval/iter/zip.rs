#![cfg_attr(not(with_main), no_std)]

#[crux_test]
pub fn f() {
    let arr = [1, 2, 3, 4];
    let arr = &arr[..];
    for (&a, &b) in arr.iter().zip(arr.iter().skip(1)) {
        assert!(a < b);
    }
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
