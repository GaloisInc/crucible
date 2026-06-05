// FAIL: read from uninitialized memory

// This test ensures that writing `MaybeUninit::uninit()` to `xs[0]` properly
// clears the aggregate entries from the tuple it originally held, which we can
// observe as a failure to read from the cleared memory.

use std::mem::MaybeUninit;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let mut xs = [MaybeUninit::new((1, 2))];
    xs[0] = MaybeUninit::uninit();
    let x = unsafe { xs[0].assume_init_read() };
    x.0 + x.1
}

pub fn main() {
    println!("{:?}", crux_test());
}
