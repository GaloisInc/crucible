extern crate crucible;
use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

#[cfg(not(with_main))]
#[cfg_attr(crux, crux_test)]
fn crux_test() {
    let N       = 2;
    let V       = 3;
    let mut children = vec![];

    for x in 0..N {
        let a = thread::spawn(move || {
            V
        });
        children.push(a);
    }

    let mut sum = 0;
    for c in children {
        sum += c.join().unwrap();
    }
    crucible_assert!(sum == N*V) ;
}

#[cfg(with_main)]
fn main() {}
