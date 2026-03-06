#![cfg_attr(not(with_main), no_std)]

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let mut xs = [0u8; 12];

    {
        let middle = &mut xs[1..11];
        // Write through first and last chunks
        let (c1, tail) = middle.split_first_chunk_mut::<4>().unwrap();
        let (mid, c2) = tail.split_last_chunk_mut::<4>().unwrap();
        assert_eq!(mid, &[0,0]);
        *c1 = [1,2,3,4];
        *c2 = [5,6,7,8];
    }

    assert_eq!(xs, [0,1,2,3,4,0,0,5,6,7,8,0]);

    {
        let middle = &mut xs[1..11];
        let (c1, tail) = middle.split_first_chunk::<4>().unwrap();
        let (mid, c2) = tail.split_last_chunk::<4>().unwrap();
        assert_eq!(c1, &[1,2,3,4]);
        assert_eq!(c2, &[5,6,7,8]);
        assert_eq!(mid, &[0,0]);
    }
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
