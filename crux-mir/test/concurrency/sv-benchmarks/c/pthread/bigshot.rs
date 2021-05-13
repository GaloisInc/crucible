extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

#[cfg(not(with_main))]
#[cfg_attr(crux, crux_test)]
fn bigshot_p() {
    let v = Arc::new(Mutex::new(None));

    let v1 = Arc::clone(&v);
    let t1 = thread::spawn(move|| {
        let mut pv = v1.lock().unwrap();
        *pv = Some("");
        v1.crucible_TEMP_unlock();
    });
    let v2 = Arc::clone(&v);
    let t2 = thread::spawn(move|| {
        let mut pv = v2.lock().unwrap();
        if let Some(_) = *pv {
            *pv = Some("Bigshot");
        }
        v2.crucible_TEMP_unlock();
    });
    t1.join();
    t2.join();

    let mut pv = v.lock().unwrap();
    if let Some(x) = *pv {
        crucible_assert!(&x[0..1] == "B"); // This fails
    }
    v.crucible_TEMP_unlock();

}

#[cfg(not(with_main))]
#[cfg_attr(crux, crux_test)]
fn bigshot_s() {
    let v = Arc::new(Mutex::new(None));

    let v1 = Arc::clone(&v);
    let t1 = thread::spawn(move|| {
        let mut pv = v1.lock().unwrap();
        *pv = Some("");
        v1.crucible_TEMP_unlock();
    });
    t1.join();
    let v2 = Arc::clone(&v);
    let t2 = thread::spawn(move|| {
        let mut pv = v2.lock().unwrap();
        if let Some(_) = *pv {
            *pv = Some("Bigshot");
        }
        v2.crucible_TEMP_unlock();
    });
    t2.join();

    let mut pv = v.lock().unwrap();
    if let Some(x) = *pv {
        crucible_assert!(&x[0..1] == "B"); // This succeeds
    }
    v.crucible_TEMP_unlock();

}

#[cfg(not(with_main))]
#[cfg_attr(crux, crux_test)]
fn bigshot_s2() {
    let v = Arc::new(Mutex::new(None));

    let v1 = Arc::clone(&v);
    let t1 = thread::spawn(move|| {
        let mut pv = v1.lock().unwrap();
        *pv = Some("");
        v1.crucible_TEMP_unlock();
    });
    t1.join();
    let v2 = Arc::clone(&v);
    let t2 = thread::spawn(move|| {
        let mut pv = v2.lock().unwrap();
        if let Some(_) = *pv {
            *pv = Some("Bigshot");
        }
        v2.crucible_TEMP_unlock();
    });
    t2.join();

    let mut pv = v.lock().unwrap();
    let x = pv.unwrap();
    crucible_assert!(&x[0..1] == "B"); // This succeeds
    v.crucible_TEMP_unlock();

}
