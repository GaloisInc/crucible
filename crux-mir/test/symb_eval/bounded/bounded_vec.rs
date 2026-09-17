#![no_std]

use alloc::vec::Vec;
use crucible::{
    crucible_assert,
    symbolic::BoundedSymbolic,
};

#[crux::test]
pub fn f() {
    const N: usize = 3;
    let bytes = Vec::<u8>::bounded_symbolic::<N>("v");
    crucible_assert!(bytes.len() <= N);
}