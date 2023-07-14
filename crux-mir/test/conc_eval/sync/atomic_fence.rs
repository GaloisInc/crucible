use std::sync::atomic::{self, AtomicI32};
use std::sync::atomic::Ordering::*;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let a = AtomicI32::new(1);
    a.store(2, SeqCst);
    atomic::fence(SeqCst);
    a.load(SeqCst)
}

pub fn main() {
    println!("{:?}", crux_test());
}
