#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::compare_bytes;

fn test_compare_bytes(
    left: *const u8,
    right: *const u8,
    bytes: usize,
    expected_res: i32,
) {
    unsafe {
        assert!(compare_bytes(left, right, bytes) == expected_res);
    }
}

fn test_compare_bytes_slices(
    left: &[u8],
    right: &[u8],
    bytes: usize,
    expected_res: i32,
) {
    test_compare_bytes(left.as_ptr(), right.as_ptr(), bytes, expected_res);
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    test_compare_bytes_slices(&[], &[], 0, 0);
    test_compare_bytes_slices(&[1], &[1], 0, 0);
    test_compare_bytes_slices(&[1], &[1], 1, 0);
    test_compare_bytes_slices(&[1], &[4], 1, -3);
    test_compare_bytes_slices(&[4], &[1], 1, 3);
    test_compare_bytes_slices(&[0, 2], &[0, 2], 2, 0);
    test_compare_bytes_slices(&[0, 1], &[0, 4], 2, -3);
    test_compare_bytes_slices(&[0, 4], &[0, 1], 2, 3);
    test_compare_bytes_slices(&[1, 1], &[4, 4], 2, -3);
    test_compare_bytes_slices(&[4, 4], &[1, 1], 2, 3);

    // Comparing 0 bytes should always succeed, even with null pointers.
    test_compare_bytes(std::ptr::null(), std::ptr::null(), 0, 0);
}

fn main() {
    println!("{:?}", crux_test());
}
