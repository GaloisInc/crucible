extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

fn run_threads() -> (i32, i32)
{
    let data1 = Arc::new(Mutex::new(10 as i32));
    let data2 = Arc::new(Mutex::new(10 as i32));

    let p1 = Arc::clone(&data1);
    let q1 = Arc::clone(&data2);
    let t1 = thread::spawn(move || {
        let mut pdata1 = p1.lock().unwrap();
        *pdata1 += 1;
        p1.crucible_TEMP_unlock();

        let mut pdata2 = q1.lock().unwrap();
        *pdata2 += 1;
        q1.crucible_TEMP_unlock();
    });

    let p2 = Arc::clone(&data1);
    let q2 = Arc::clone(&data2);
    let t2 = thread::spawn(move || {
        let mut pdata1 = p2.lock().unwrap();
        *pdata1 += 5;
        p2.crucible_TEMP_unlock();

        let mut pdata2 = q2.lock().unwrap();
        *pdata2 -= 6;
        q2.crucible_TEMP_unlock();
    });

    t1.join();
    t2.join();

    let pdata1 = data1.lock().unwrap();
    let pdata2 = data2.lock().unwrap();
    let r = (*pdata1, *pdata2);
    data1.crucible_TEMP_unlock();
    data2.crucible_TEMP_unlock();

    return r
}

#[crux::test]
fn stateful01_1()
{
    let (d1, d2) = run_threads();
    crucible_assert!( !(d1 == 16 && d2 == 5) );
}

#[crux::test]
fn stateful01_2()
{
    let (d1, d2) = run_threads();
    crucible_assert!( !(d1 != 16 && d2 != 5) );
}
