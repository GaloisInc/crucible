use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::*;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let a = AtomicI32::new(1);
    let mut i = 1;
    for &ordering in &[Relaxed, Release, Acquire, AcqRel, SeqCst] {
        let old = a.compare_and_swap(2, 5, ordering);
        assert!(old == 1);
    }
    for &ordering in &[Relaxed, Release, Acquire, AcqRel, SeqCst] {
        let old = a.compare_and_swap(i, i + 1, ordering);
        assert!(old == i);
        i += 1;
    }
    a.load(SeqCst)
}

pub fn main() {
    println!("{:?}", crux_test());
}
