#![cfg_attr(not(with_main), no_std)]

#[cfg_attr(crux, crux::test)]
pub fn f() -> [u8; 7] {
    let mut arr = [1, 2, 3, 4, 5, 6, 7];
    let (chunks, remainder) = arr.as_chunks_mut::<3>();
    chunks[0] = chunks[1];
    chunks[1][0] = 99;
    arr
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
