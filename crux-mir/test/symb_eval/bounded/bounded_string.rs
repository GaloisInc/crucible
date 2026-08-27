#![no_std]

use alloc::string::String;
use crucible::{
    crucible_assert,
    symbolic::BoundedSymbolic,
};

#[crux::test]
pub fn f() {
    const N: usize = 3;
    let s = String::bounded_symbolic::<N>("s");
    crucible_assert!(s.len() <= N);
}