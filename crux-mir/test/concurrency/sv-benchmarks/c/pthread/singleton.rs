extern crate crucible;

use crucible::*;
use std::thread;
use std::ptr;
use std::sync::{Arc,Mutex,};

fn thread1(v: Arc<Mutex<Option<i32>>>) {
    let mut p = v.lock().unwrap();
    *p = Some(0);
    v.crucible_TEMP_unlock();
}

fn thread2(v: Arc<Mutex<Option<i32>>>) {
    let mut p = v.lock().unwrap();
    let _ = p.unwrap();
    *p = Some(1);
    v.crucible_TEMP_unlock();
}
fn thread3(v: Arc<Mutex<Option<i32>>>) {
    let mut p = v.lock().unwrap();
    let _ = p.unwrap();
    *p = Some(2);
    v.crucible_TEMP_unlock();
}

fn thread0(v: Arc<Mutex<Option<i32>>>) {
    let v1 = v.clone();
    let t1 = thread::spawn(move|| thread1(v1));
    t1.join();

    let mut ts = vec![];
    for i in 0..4 {
        let vi = v.clone();
        ts.push(thread::spawn(
            move || {
                if i == 1 {
                    thread3(vi);
                }  else {
                    thread2(vi);
                }
            }));
    }
    for t in ts {
        t.join();
    }
}

#[cfg_attr(crux, crux_test)]
fn singleton() {
    let v = Arc::new(Mutex::new(None));
    let vv = v.clone();
    let t0 = thread::spawn(move|| thread0(vv));
    t0.join();

    let mut p = v.lock().unwrap();
    let x = p.unwrap();
    crucible_assert!(x == 1);
    v.crucible_TEMP_unlock();
}
