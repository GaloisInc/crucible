#![cfg_attr(not(with_main), no_std)]

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut arr = [1, 2, 3];
    let arr: &mut [_] = &mut arr;
    let mut sum = 0;
    for x in &mut *arr {
        *x += 1;
        sum += *x;
    }
    assert!(sum == 9);
    assert!(arr == [2, 3, 4]);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
