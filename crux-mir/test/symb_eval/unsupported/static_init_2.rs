// An example where crucible-mir fails to translate a static item's constant
// value and then attempts to access it during simulation, resulting in an
// error. Contrast this with static_init.rs, where mir-json itself fails to
// render a static item's value---in this example, mir-json /does/ render the
// value successfully, but crucible-mir is the one that fails to translate it
// properly.
//
// This test case primarily exists to track the error message that crucible-mir
// produces in this scenario, which is currently somewhat poor. If
// https://github.com/GaloisInc/crucible/issues/1891 is addressed, then we will
// need to update the expected test output here.
//
// It is possible that a future version of crucible-mir will be capable of
// simulating `extern` functions (see
// https://github.com/GaloisInc/mir-json/issues/61 for a prerequisite). If so,
// then we should rewrite this test case to use a different feature that
// crucible-mir does not support. (Make sure to also update
// test/conc_eval/statics/static_unsupported_translation.rs, which also relies
// on `extern` functions.)

use core::ffi::*;

extern "C" {
    fn abs(x: c_int) -> c_int;
}

pub static ABS: unsafe extern "C" fn(c_int) -> c_int = abs;

pub fn foo() -> c_int {
    unsafe { ABS(-1) }
}

#[crux::test]
pub fn test() -> c_int {
    foo()
}
