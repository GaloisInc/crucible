// FAIL: division not exact triggers UB
#![feature(core_intrinsics)]
#![cfg_attr(not(with_main), no_std)]
extern crate core;

fn f(x: u32) -> u32 {
    // Division not exact → should trigger UB
    unsafe { core::intrinsics::exact_div(x, 3) }
}

const ARG: u32 = 10;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}

#[cfg(not(with_main))]
#[cfg_attr(crux, crux::test)]
#[should_panic(expected = "undefined behavior")]
fn crux_test() -> u32 {
    f(ARG)
}
