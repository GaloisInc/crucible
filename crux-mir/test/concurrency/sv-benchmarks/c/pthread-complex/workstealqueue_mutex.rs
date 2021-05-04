extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};
use std::sync::atomic::AtomicU16;
use std::sync::atomic::Ordering::SeqCst;

struct Obj {
    field: i32,
}

impl Obj {
    fn new() -> Obj {
        Obj { field: 0 }
    }

    fn init(&mut self) {
        self.field = 0;
    }

    fn operation(&mut self) {
        self.field += 1;
    }

    fn check(&self) {
        crucible_assert(self.field == 1);
    }
}


struct WorkStealQueue {
    maxSize: i64,
    initialSize: i64,
    elems: Vec<Obj>,
    mask: i64,
    head: Arc<AtomicI64>,
    tail: Arc<AtomicI64>,
}

impl WorkStealQueue {
    fn new(size: i64) -> WorkStealQueue {
        WorkStealQueue {
            maxSize = 1024*1024,
            initialSize = 1024,
            elems = Vec::with_capacity(1024),
            mask = size - 1,
            head = Arc::new(AtomicUsize::new(0)),
            tail = Arc::new(AtomicUsize::new(0)),
        }
    }
}
