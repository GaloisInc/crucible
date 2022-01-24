extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex,};
use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::SeqCst;


static data1: AtomicI32 = AtomicI32::new(0);
static data2: AtomicI32 = AtomicI32::new(0);

fn func_a(lock1: Arc<Mutex<()>>, lock2: Arc<Mutex<()>>) {
    let l = lock1.lock().unwrap();
    data1.store(1, SeqCst);
    lock1.crucible_TEMP_unlock();

    let l2 = lock2.lock().unwrap();
    data2.store(data1.load(SeqCst)+1, SeqCst);
    lock2.crucible_TEMP_unlock();
}


fn func_b(lock1: Arc<Mutex<()>>, lock2: Arc<Mutex<()>>) {
    let mut t1 = -1;
    let mut t2 = -1;

    let l = lock1.lock().unwrap();
    if data1.load(SeqCst) == 0 {
        lock1.crucible_TEMP_unlock();
        return ();
    }
    t1 = data1.load(SeqCst);
    lock1.crucible_TEMP_unlock();

    let l2 = lock2.lock().unwrap();
    t2 = data2.load(SeqCst);
    lock2.crucible_TEMP_unlock();

    crucible_assert!(t2 == t1 + 1);
}

fn twostage_test(t_threads: usize, r_threads: usize) {
    let lock1 = Arc::new(Mutex::new(()));
    let lock2 = Arc::new(Mutex::new(()));
    let mut threads = vec![];
    for i in 0..t_threads {
        let l1 = lock1.clone();
        let l2 = lock2.clone();
        threads.push(thread::spawn(move|| func_a(l1, l2)));
    }
    for i in 0..r_threads {
        let l1 = lock1.clone();
        let l2 = lock2.clone();
        threads.push(thread::spawn(move|| func_b(l1, l2)));
    }
    for t in threads {
        t.join();
    }
}

#[cfg_attr(crux, crux_test)]
fn twostage_3() {
    twostage_test(2,1);
}
