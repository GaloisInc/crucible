// FAIL: Should panic, but doesn't
#![cfg_attr(not(with_main), no_std)]
extern crate core;
#[allow(exceeding_bitshifts)]
fn f(x: i64) -> i64 {
    x << 64i64
}

const ARG: i64 = 1;

#[cfg(with_main)]
pub fn main() {
    use core::panic;
    let result = panic::catch_unwind(|| {
        println!("{:?}", f(ARG));
    });
    match result {
        Ok(r) => println!("{:?}", r),
        Err(_) => println!("<<PANIC>>"),
    };
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i64 { f(ARG) }
