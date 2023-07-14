extern crate crucible;
use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};
use std::sync::atomic::AtomicU16;
use std::sync::atomic::Ordering::SeqCst;

#[cfg(not(with_main))]
#[crux::test]
fn crux_test_nofail() {
    let data    = Arc::new(Mutex::new(()));
    let ctr     = Arc::new(AtomicU16::new(0));

    let N       = 3;
    let mut children = vec![];

    for x in 0..N {
        let d = Arc::clone(&data);
        let c = Arc::clone(&ctr);
        let a = thread::spawn(move || {
            let p = d.lock().unwrap();
            c.fetch_add(1, SeqCst);
            c.fetch_add(1, SeqCst);
            // Until crux-mir supports drop()
            d.crucible_TEMP_unlock();

            ()
        });
        children.push(a);
    }

    let p = data.lock().unwrap();
    let v = ctr.load(SeqCst);

    crucible_assert!(v % 2 == 0); // Correct

    // Until crux-mir supports drop()
    data.crucible_TEMP_unlock();
}
