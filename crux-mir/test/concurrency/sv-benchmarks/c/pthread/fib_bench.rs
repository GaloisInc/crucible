extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

const Num : i32 = 3;

fn t1(m : Arc<Mutex<(i32,i32)>>) {
    for k in 0..Num {
        let mut p = m.lock().unwrap();
        let (i, j) = *p;
        *p = (i+j, j);
        m.crucible_TEMP_unlock();
    }
}

fn t2(m : Arc<Mutex<(i32,i32)>>) {
    for k in 0..Num {
        let mut p = m.lock().unwrap();
        let (i, j) = *p;
        *p = (i, i+j);
        m.crucible_TEMP_unlock();
    }
}

fn calc_fib() -> i32 {
    let mut i = 1;
    let mut j = 1;
    for _ in 0..2*Num {
        let tmp = j;
        j = i + j;
        i = tmp;
    }
    j
}

#[cfg_attr(crux, crux_test)]
fn crux_test_fail() {
    let data    = Arc::new(Mutex::new((1 as i32, 1 as i32)));

    let d1 = Arc::clone(&data);
    let h1 = thread::spawn(move || {
        t1(d1);
    });
    let d2 = Arc::clone(&data);
    let h2 = thread::spawn(move || {
        t2(d2);
    });

    h1.join();
    h2.join();

    let p = data.lock().unwrap();
    let (i,j) = *p;
    let bound = calc_fib();
    crucible_assert!( !((i >= bound) || (j >= bound)) );
    // Until crux-mir supports drop()
    data.crucible_TEMP_unlock();
}

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    let data = Arc::new(Mutex::new((1 as i32, 1 as i32)));

    let d1 = Arc::clone(&data);
    let h1 = thread::spawn(move || {
        t1(d1);
    });

    let d2 = Arc::clone(&data);
    let h2 = thread::spawn(move || {
        t2(d2);
    });

    h1.join();
    h2.join();

    let p = data.lock().unwrap();
    let (i,j) = *p;
    let bound = calc_fib();
    // Until crux-mir supports drop()
    data.crucible_TEMP_unlock();
    crucible_assert!( !((i > bound) || (j > bound)) );
}
