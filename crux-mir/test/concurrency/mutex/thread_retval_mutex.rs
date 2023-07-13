extern crate crucible;
use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

#[cfg(not(with_main))]
#[crux::test]
fn crux_test() {
    let data    = Arc::new(Mutex::new(0 as u32));
    let N       = 3;
    let mut children = vec![];

    for x in 0..N {
        let d = Arc::clone(&data);
        let a = thread::spawn(move || {
            let mut p = d.lock().unwrap();
            *p += x;
            *p
        });
        children.push(a);
    }

    let mut sum = 0;
    for c in children {
        sum += c.join().unwrap();
    }
    // Should fail!
    crucible_assert!(sum >= 3);
}

#[cfg(with_main)]
fn main() {}
