#![feature(core_intrinsics)]
#![cfg_attr(not(with_main), no_std)]
extern crate core;

fn f(x: i32) -> i32 {
    // Should divide exactly
    unsafe { core::intrinsics::exact_div(x, 3) }
}

const ARG: i32 = 12;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}

#[cfg(not(with_main))]
#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    f(ARG)
}
