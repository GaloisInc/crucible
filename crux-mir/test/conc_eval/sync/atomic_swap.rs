use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::*;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let a = AtomicI32::new(1);
    a.store(2, SeqCst);
    let x = a.swap(1, SeqCst);
    let y = a.load(SeqCst);
    (x, y)
}

pub fn main() {
    println!("{:?}", crux_test());
}
