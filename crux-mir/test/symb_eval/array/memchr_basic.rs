// A regression test for https://github.com/GaloisInc/mir-json/issues/311. This
// simultaneously tests multiple things:
//
// * This tests that mir-json has patched its vendored-in copy of the `memchr`
//   crate to replace its inline assembly-based `memchr` implementation (which
//   crucible-mir has no hope of simulating) with a fallback implementation
//   that works on all architectures.
//
// * Moreover, it ensures that crucible-mir is capable of simulating the
//   fallback implementation, which relies on comparing pointers that are
//   ultimately derived from the same backing allocation.
#![feature(rustc_private)]

extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() {
    crucible_assert!(memchr::memchr(1, &[]) == None);
    crucible_assert!(memchr::memchr(1, &[0]) == None);
    crucible_assert!(memchr::memchr(1, &[0, 2]) == None);
    crucible_assert!(memchr::memchr(1, &[1]) == Some(0));
    crucible_assert!(memchr::memchr(1, &[1, 0]) == Some(0));
    crucible_assert!(memchr::memchr(1, &[1, 1]) == Some(0));
    crucible_assert!(memchr::memchr(1, &[0, 1]) == Some(1));
}
