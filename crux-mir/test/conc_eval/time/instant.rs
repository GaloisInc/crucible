//! Check that `Instant` can be used without triggering a panic or FFI call.
use std::time::Instant;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let start = Instant::now();
    let dur = start.elapsed();
    let dur2 = Instant::now().duration_since(start);
    // There's nothing sensible to return here - any output based on `Instant` will fail to match
    // the oracle output.
}

pub fn main() { println!("{:?}", crux_test()); }
