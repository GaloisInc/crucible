extern crate crucible;
use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

#[cfg(not(with_main))]
#[cfg_attr(crux, crux_test)]
fn crux_test_nofail() {
    let data    = Arc::new(Mutex::new(0 as u32));
    let N       = 3;
    let mut children = vec![];

    for x in 0..N {
        let d = Arc::clone(&data);
        let a = thread::spawn(move || {
            let mut p = d.lock().unwrap();

            *p += x;
            // Until crux-mir supports drop()
            d.crucible_TEMP_unlock();

            ()
        });
        children.push(a);
    }

    for c in children {
        let x = c.join();
    }

    let p = data.lock().unwrap();
    let sum = N*(N-1)/2;

    crucible_assert!(*p == sum); // Correct

    // Until crux-mir supports drop()
    data.crucible_TEMP_unlock();
}

#[cfg_attr(crux, crux_test)]
fn crux_test_fail() {
    let data    = Arc::new(Mutex::new(0 as u32));
    let N       = 2;
    let mut children = vec![];

    for x in 0..N {
        let d = Arc::clone(&data);
        let a = thread::spawn(move || {

            let mut p = d.lock().unwrap();
            let b     = bool::symbolic("b");

            if b { *p += x; }

            d.crucible_TEMP_unlock();

            ()
        });
        children.push(a);
    }
    for c in children {
        let x = c.join();
    }

    let p = data.lock().unwrap();
    let sum = N*(N-1)/2;
    crucible_assert!(*p == sum);
    data.crucible_TEMP_unlock();
}


#[cfg(with_main)]
fn main() {}
