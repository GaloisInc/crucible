#![cfg_attr(not(with_main), no_std)]

#[crux_test]
pub fn f() {
    let arr = [1, 2, 3, 4];
    let sum: usize = arr.iter().cloned().sum();
    assert!(sum == 10);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
