extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex,};
use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::SeqCst;

const NUM: i32 = 1;
const LIMIT: i32 = (2*NUM + 6);

static i: AtomicI32 = AtomicI32::new(3);
static j: AtomicI32 = AtomicI32::new(6);

fn t1(m:Arc<Mutex<()>>)
{
    for k in 0..NUM {
        m.lock().unwrap();

        i.store(1+j.load(SeqCst), SeqCst);

        m.crucible_TEMP_unlock();
    }
}

fn t2(m:Arc<Mutex<()>>)
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
    let m = Arc::new(Mutex::new(()));

    {
        let mm = m.clone();
        thread::spawn(move || t1(mm));
    }
    {
        let mm = m.clone();
        thread::spawn(move || t2(mm));
    }

    let condI = i.load(SeqCst) > LIMIT;
    let condJ = j.load(SeqCst) > LIMIT;

    crucible_assert!(! (condI || condJ) );
}

#[crux::test]
fn triangular_2()
{
    let m = Arc::new(Mutex::new(()));

    {
        let mm = m.clone();
        thread::spawn(move || t1(mm));
    }
    {
        let mm = m.clone();
        thread::spawn(move || t2(mm));
    }

    let condI = i.load(SeqCst) >= LIMIT;
    let condJ = j.load(SeqCst) >= LIMIT;

    crucible_assert!(! (condI || condJ) );
}
