use std::sync::LazyLock;
use std::sync::atomic::{AtomicI32, Ordering};

static X: AtomicI32 = AtomicI32::new(1);
static LL: LazyLock<i32> = LazyLock::new(|| 2 + X.load(Ordering::Relaxed));

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    X.store(2, Ordering::Relaxed);
    let y = *LL;
    X.store(3, Ordering::Relaxed);
    let z = *LL;
    // Both should be 4, since `X` was 2 at the time the `LazyLock` was forced.
    (y, z)
}

pub fn main() {
    println!("{:?}", crux_test());
}
