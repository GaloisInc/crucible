extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex,};
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::SeqCst;

/* The complexity in this benchmark is due to the fact that we currently perform
 * NO path merging. Hence, we need to explore an exponential number of
 * executions due to the branch in the for-loop in find_entries.
 */
const ARRAYSIZE:usize = 6;
const NUM_THREADS:usize = 2;

const iterations:usize = ARRAYSIZE/NUM_THREADS;

fn find_entries(tid:usize,
                search_no:u32,
                arr:Arc<Vec<AtomicU32>>,
                count:Arc<Mutex<usize>>)
{
    let     start = tid*iterations;
    let     end   = start + iterations;

    let mut local_count = 0;

    for i in start..end
    {
        if arr[i].load(SeqCst) == search_no {
            local_count += 1;
        }
    }

    let mut pcount = count.lock().unwrap();
    *pcount += local_count;
    count.crucible_TEMP_unlock();
}

#[cfg_attr(crux, crux::test)]
fn pthread_finding_k_matches()
{
    let mut vals = vec![];
    let mut thds = vec![];
    for i in 0..ARRAYSIZE {
        vals.push(AtomicU32::new((i as u32) % 10 + (1.0 as u32)))
    }


    let arr   = Arc::new(vals);
    let count = Arc::new(Mutex::new(0));

    let search_no = u32::symbolic("search_no");

    for i in 0..NUM_THREADS {
        let parr = arr.clone();
        let mcount = count.clone();
        thds.push(thread::spawn(
            move || find_entries(i, search_no, parr, mcount)
        ));
    }

    for t in thds {
        t.join();
    }

    let mut temp = 0;
    for i in 0..ARRAYSIZE {
        if arr[i].load(SeqCst) == search_no {
            temp += 1;
        }
    }

    let c = count.lock().unwrap();
    crucible_assert!(*c == temp); // True!
}
