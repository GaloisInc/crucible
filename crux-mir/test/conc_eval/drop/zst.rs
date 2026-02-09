//! Test drop for zero-sized types.
use std::sync::atomic::{AtomicUsize, Ordering};

static DROPPED: AtomicUsize = AtomicUsize::new(0);

struct S;
impl Drop for S {
    fn drop(&mut self) {
        DROPPED.fetch_add(1, Ordering::Relaxed);
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    {
        let s = S;
        let s2 = (S,);
        drop(s2);
    }
    DROPPED.load(Ordering::Relaxed)
}

pub fn main() {
    println!("{:?}", crux_test());
}
