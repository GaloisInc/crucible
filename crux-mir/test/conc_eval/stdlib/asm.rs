// A regression test for #1520. While crucible-mir doesn't support simulating
// inline assembly (via the asm! macro), it should at least be able to
// translate it without crashing. This test case ensures that this happens.

use std::arch::asm;

fn f(x: bool) -> u32 {
    if x {
        unsafe { asm!(""); }
        1
    } else {
        0
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u32 {
    f(false)
}

pub fn main() {
    println!("{:?}", crux_test());
}
