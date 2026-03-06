#![cfg_attr(not(with_main), no_std)]

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let mut xs = [0u8; 10];

    // Write through first and last chunks
    *xs.first_chunk_mut().unwrap() = [42,10,20,30];
    *xs.last_chunk_mut().unwrap() = [1,2,3,4];

    assert_eq!(xs, [42,10,20,30,0,0,1,2,3,4]);

    // Read through first and last chunks
    assert_eq!(xs.first_chunk(), Some(&[42,10,20,30]));
    assert_eq!(xs.last_chunk(), Some(&[1,2,3,4]));
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
