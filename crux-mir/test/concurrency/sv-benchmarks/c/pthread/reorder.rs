extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex,};
use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::SeqCst;

static a: AtomicI32 = AtomicI32::new(0);
static b: AtomicI32 = AtomicI32::new(0);

fn set_thread() {
    a.store(1, SeqCst);
    b.store(-1, SeqCst);
}

fn check_thread() {
    let cond =
        ((a.load(SeqCst) == 0 && b.load(SeqCst) == 0) ||
         (a.load(SeqCst) == 1 && b.load(SeqCst) == -1));
    crucible_assert!(cond);
}

fn run_test(numSet: usize, numCheck: usize) {
    let mut threads = vec![];

    for i in 0..(numSet/2) {
        threads.push(thread::spawn(|| set_thread() ));
    }
    for i in 0..numCheck {
        threads.push(thread::spawn(|| check_thread() ));
    }
    for i in numSet/2..numSet {
        threads.push(thread::spawn(|| set_thread() ));
    }

    for t in threads {
        t.join();
    }
}

#[cfg_attr(crux, crux_test)]
fn reorder2() {
    run_test(2,2);
}

#[cfg_attr(crux, crux_test)]
fn reorder5() {
    run_test(4,1);
}
