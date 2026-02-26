#![cfg_attr(not(with_main), no_std)]

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let arr = [1, 2, 3, 4, 5, 6, 7];
    let (chunks, remainder) = arr.as_chunks::<3>();
    assert!(chunks == &[[1,2,3],[4,5,6]]);
    assert!(remainder == &[7]);
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
