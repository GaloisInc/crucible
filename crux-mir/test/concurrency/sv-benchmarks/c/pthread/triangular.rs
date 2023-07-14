extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex,};
use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::SeqCst;

const NUM: i32 = 1;
const LIMIT: i32 = (2*NUM + 6);

fn t1(i:Arc<AtomicI32>, j:Arc<AtomicI32>, m:Arc<Mutex<()>>)
{
    for k in 0..NUM {
        m.lock().unwrap();

        i.store(1+j.load(SeqCst), SeqCst);

        m.crucible_TEMP_unlock();
    }
}

fn t2(i:Arc<AtomicI32>, j:Arc<AtomicI32>, m:Arc<Mutex<()>>)
{
    for k in 0..NUM {
        m.lock().unwrap();

        j.store(1+i.load(SeqCst), SeqCst);

        m.crucible_TEMP_unlock();
    }
}

#[crux::test]
fn triangular_1()
{
    let i = Arc::new(AtomicI32::new(3));
    let j = Arc::new(AtomicI32::new(6));

    let m = Arc::new(Mutex::new(()));

    {
        let ii = i.clone();
        let jj = j.clone();
        let mm = m.clone();
        thread::spawn(move || t1(ii, jj, mm));
    }
    {
        let ii = i.clone();
        let jj = j.clone();
        let mm = m.clone();
        thread::spawn(move || t2(ii,jj,mm));
    }

    let condI = i.load(SeqCst) > LIMIT;
    let condJ = j.load(SeqCst) > LIMIT;

    crucible_assert!(! (condI || condJ) );
}

#[crux::test]
fn triangular_2()
{
    let i = Arc::new(AtomicI32::new(3));
    let j = Arc::new(AtomicI32::new(6));

    let m = Arc::new(Mutex::new(()));

    {
        let ii = i.clone();
        let jj = j.clone();
        let mm = m.clone();
        thread::spawn(move || t1(ii, jj, mm));
    }
    {
        let ii = i.clone();
        let jj = j.clone();
        let mm = m.clone();
        thread::spawn(move || t2(ii,jj,mm));
    }

    let condI = i.load(SeqCst) >= LIMIT;
    let condJ = j.load(SeqCst) >= LIMIT;

    crucible_assert!(! (condI || condJ) );
}
