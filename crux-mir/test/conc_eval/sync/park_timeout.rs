use std::thread;
use std::time::Duration;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    // Park with a very short timeout exercises the blocking path but doesn't block for long enough
    // to make the test suite slow.
    thread::park_timeout(Duration::from_millis(10));
    thread::park_timeout(Duration::from_millis(10));
    1
}

pub fn main() {
    println!("{:?}", crux_test());
}
