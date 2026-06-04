//! These test cases are meant to exercise reading, or failing to read, elements
//! and sub-aggregate at symbolic offsets within a `MirAggregate`.

extern crate crucible;
use crucible::Symbolic as _;

use std::mem::{size_of, size_of_val};

// A replacement for `ptr::byte_add`, whose uses `crucible-mir` can't translate.
// See https://github.com/GaloisInc/crucible/issues/1844.
unsafe fn byte_add<T>(p: *const T, off: usize) -> *const T {
    p.cast::<u8>().add(off).cast::<T>()
}

static XS: [(u32, u32); 3] = [(1, 2), (3, 4), (5, 6)];
static YS: &'static [(u32, u32)] = &XS;

#[crux::test]
fn index() -> (u32, u32) {
    let idx = usize::symbolic_where("idx", |&idx| idx < YS.len());
    YS[idx]
}

#[crux::test]
fn offset_ag() -> [u32; 2] {
    // A byte offset into `XS`/`YS` from which it should always be valid to read
    // a `[u32; 2]`.
    let off = usize::symbolic_where("off", |&off| {
        off < size_of_val(&XS) - size_of::<[u32; 2]>() && off % 4 == 0
    });

    unsafe { *(byte_add(YS.as_ptr().cast::<[u32; 2]>(), off)) }
}

#[crux::test]
fn offset_single() -> u32 {
    // A byte offset into `XS`/`YS` from which it should always be valid to read
    // a single `u32`.
    let off = usize::symbolic_where("off", |&off| {
        off < size_of_val(&XS) - size_of::<u32>() && off % 4 == 0
    });

    unsafe { *(byte_add(YS.as_ptr().cast::<u32>(), off)) }
}

#[crux::test]
fn fail_offset_ag() -> [u32; 2] {
    // A byte offset into `XS`/`YS` from which it should be potentially invalid
    // to read a `[u32; 2]`.
    let off = usize::symbolic_where("off", |&off| off < size_of_val(&XS) - size_of::<[u32; 2]>());

    unsafe { *(byte_add(YS.as_ptr().cast::<[u32; 2]>(), off)) }
}

#[crux::test]
fn fail_offset_single() -> u32 {
    // A byte offset into `XS`/`YS` from which it should be potentially invalid
    // to read a `u32`.
    let off = usize::symbolic_where("off", |&off| off < size_of_val(&XS) - size_of::<u32>());

    unsafe { *(byte_add(YS.as_ptr().cast::<u32>(), off)) }
}
