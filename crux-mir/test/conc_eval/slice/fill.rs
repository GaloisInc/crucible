fn slice_fill_test<T: Copy + PartialEq>(s: &mut [T], x: T) {
    s.fill(x);
    assert!(s.iter().all(|&y| x == y));
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    slice_fill_test(&mut [0; 2], 1i8);
    slice_fill_test(&mut [0; 2], 1i16);
    slice_fill_test(&mut [0; 2], 1i32);
    slice_fill_test(&mut [0; 2], 1i64);
    slice_fill_test(&mut [0; 2], 1i128);
    slice_fill_test(&mut [0; 2], 1u8);
    slice_fill_test(&mut [0; 2], 1u16);
    slice_fill_test(&mut [0; 2], 1u32);
    slice_fill_test(&mut [0; 2], 1u64);
    slice_fill_test(&mut [0; 2], 1u128);
}

pub fn main() {
    println!("{:?}", crux_test());
}
