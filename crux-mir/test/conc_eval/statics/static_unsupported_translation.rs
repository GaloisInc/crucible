// A regression test for #1534. At present, crucible-mir doesn't support
// simulating `extern` functions like `abs`, which means that crucible-mir
// cannot faithfully model the definition of the `ABS` static. Nevertheless, we
// don't want this to interrupt simulating the `foo` function, as we can
// simulate the `else` branch (which doesn't access `ABS`) without issue.
//
// It is possible that a future version of crucible-mir will be capable of
// simulating `extern` functions (see
// https://github.com/GaloisInc/mir-json/issues/61 for a prerequisite). If so,
// then we should rewrite this test case to use a different feature that
// crucible-mir does not support. (Make sure to also update
// test/symb_eval/unsupported/static_init_2.rs, which also relies on `extern`
// functions.)

use core::ffi::*;

extern "C" {
    fn abs(x: c_int) -> c_int;
}

pub static ABS: unsafe extern "C" fn(c_int) -> c_int = abs;

pub fn foo(b: bool) -> c_int {
    if b {
        unsafe { ABS(-1) }
    } else {
        2
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> c_int {
    foo(false)
}

pub fn main() {
    println!("{:?}", crux_test());
}
