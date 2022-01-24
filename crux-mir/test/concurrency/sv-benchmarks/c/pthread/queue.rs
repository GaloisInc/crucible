extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

const SIZE : usize = 4;

struct Queue {
    elems: Vec<i32>,
    head: usize,
    tail: usize,
    amount: usize,
    // Control:
    enqueue_flag: bool,
    dequeue_flag: bool,
    // History:
    stored: Vec<i32>
}

impl Queue {
    fn new() -> Queue {
        Queue {
            elems : vec![0; SIZE],
            head  : 0,
            tail  : 0,
            amount : 0,
            enqueue_flag: false,
            dequeue_flag: false,
            stored : vec![],
        }
    }

    fn empty(&self) -> bool {
        self.head == self.tail
    }

    fn full(&self) -> bool {
        self.amount == SIZE
    }

    fn enqueue(&mut self, e: i32) {
        self.elems[self.tail] = e;
        self.amount += 1;
        self.tail =
          if self.tail == SIZE {
              1
          } else {
              self.tail + 1
          };
    }

    fn dequeue(&mut self) -> i32 {
        let x = self.elems[self.head];
        self.amount -= 1;
        self.head =
          if (self.head == SIZE) {
              1
          } else {
              self.head + 1
          };

        x
    }
}

fn t1_bad(m : Arc<Mutex<Queue>>) {
    let val = i32::symbolic("val");
    {
        let mut pq = m.lock().unwrap();
        pq.enqueue(val);
        pq.stored.push(val);
        crucible_assert!( !pq.empty() );
    }

    for i in 0..SIZE-1 {
        let mut pq = m.lock().unwrap();
        if pq.enqueue_flag {
            let val2 = i32::symbolic("val2");
            pq.enqueue(val2);
            pq.stored.push(val2);
            pq.enqueue_flag = false;
            pq.dequeue_flag = true;
        }
    }
}

fn t1(m : Arc<Mutex<Queue>>) {
    let mut pq = m.lock().unwrap();
    if pq.enqueue_flag {
        for i in 0..SIZE {
            if pq.enqueue_flag {
                let val = i32::symbolic("val2");
                pq.enqueue(val);
                pq.stored.push(val);
            }
        }
        pq.enqueue_flag = false;
        pq.dequeue_flag = true;
    }
}

fn t2(m : Arc<Mutex<Queue>>) {
    let mut pq = m.lock().unwrap();
    if pq.dequeue_flag {
        for i in 0..SIZE {
            if !pq.empty() {
                crucible_assert!(pq.dequeue() == pq.stored[i]);
            }
        }
    }
    pq.dequeue_flag = false;
    pq.enqueue_flag = true;
}

fn t2_bad(m : Arc<Mutex<Queue>>) {
    for i in 0..SIZE {
        let mut pq = m.lock().unwrap();
        if pq.dequeue_flag {
            let v = pq.dequeue();
            crucible_assert!(!(i < pq.stored.len()) || v == pq.stored[i]);
            pq.enqueue_flag = true;
            pq.dequeue_flag = false;
        }
    }
}

#[cfg_attr(crux, crux_test)]
fn crux_test_fails() {
    let mut q = Queue::new();
    q.enqueue_flag = true;
    q.dequeue_flag = false;

    crucible_assert!(q.empty());

    let data = Arc::new(Mutex::new(q));
    let d1   = data.clone();
    let d2   = data.clone();

    let h1 = thread::spawn(move || {
        t1_bad(d1.clone());
    });

    let h2 = thread::spawn(move || {
        t2_bad(d2.clone());
    });

    h1.join();
    h2.join();
}

#[cfg_attr(crux, crux_test)]
fn crux_test_succeeds() {
    let mut q = Queue::new();
    q.enqueue_flag = true;
    q.dequeue_flag = false;

    crucible_assert!(q.empty());

    let data = Arc::new(Mutex::new(q));
    let d1   = data.clone();
    let d2   = data.clone();

    let h1 = thread::spawn(move || {
        t1(d1.clone());
    });

    let h2 = thread::spawn(move || {
        t2(d2.clone());
    });

    h1.join();
    h2.join();
}
