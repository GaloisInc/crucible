extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

const SIZE:i32 = 128;
const MAX:i32 = 4;
const NUM_THREADS:usize = 10;

fn cas(tab:&Arc<Vec<Mutex<i32>>>, h:usize, val:i32, new_val:i32) -> i32
{
    let mut ret_val = 0;

    let mut table_val = tab[h].lock().unwrap();

    if *table_val == val {
        *table_val = new_val;
        ret_val = 1;
    }

    tab[h].crucible_TEMP_unlock();
    return ret_val;
}

#[cfg(not(with_main))]
#[cfg_attr(crux, crux_test)]
fn indexer() {
    let mut tab = vec![];
    let mut ts  = vec![];
    for i in 0..SIZE {
        tab.push(Mutex::new(0));
    }
    let tref = Arc::new(tab);
    for i in 0..NUM_THREADS {
        let tid = i as i32;
        let tcopy = Arc::clone(&tref);
        ts.push(thread::spawn(move|| {
            let mut m:i32 = 0;
            let mut w:i32 = 0;
            let mut h:i32 = 0;
            while (m < MAX) {
                m += 1;
                w = m*11 + tid;

                h = (w * 7) % SIZE;

                crucible_assert!(h >= 0);

                while (cas(&tcopy, h as usize, 0, w) == 0) {
                    h = (h + 1) % SIZE;
                }
            }
        }));
    }

    for t in ts {
        t.join();
    }
}
