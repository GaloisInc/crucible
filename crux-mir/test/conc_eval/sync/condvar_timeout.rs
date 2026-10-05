// FAIL: uses clock_nanosleep syscall
use std::sync::{Mutex, Condvar};
use std::time::Duration;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let m = Mutex::new(1);
    let cv = Condvar::new();

    let g = m.lock().unwrap();
    let (g, timeout) = cv.wait_timeout(g, Duration::from_millis(10)).unwrap();
    assert!(timeout.timed_out(), "spurious wakeup");

    let x = *g;
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
