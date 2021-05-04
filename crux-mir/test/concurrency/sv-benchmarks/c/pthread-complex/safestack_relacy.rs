extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::Arc;
use std::sync::atomic;
use std::sync::atomic::Ordering::SeqCst;


struct SafeStackItem {
    next: atomic::AtomicI32,
    value: atomic::AtomicI32,
}

struct SafeStack {
    array: Vec<SafeStackItem>,
    head: atomic::AtomicI32,
    count: atomic::AtomicI32,
}

impl SafeStack {
    fn new(push_count: i32) -> SafeStack {
        let mut v : Vec<SafeStackItem> = vec![];
        for i in 0..push_count-1 {
            v.push(
                SafeStackItem
                { value: atomic::AtomicI32::new(0),
                  next: atomic::AtomicI32::new(i+1),
                }
            );
        }
        v.push(
            SafeStackItem
            { value: atomic::AtomicI32::new(0),
              next: atomic::AtomicI32::new(-1),
            }
        );
        crucible_assert!(v.len() == push_count as usize);

        SafeStack
        { count: atomic::AtomicI32::new(push_count),
          head: atomic::AtomicI32::new(0),
          array: v,
        }
    }


    fn pop(&self) -> i32 {
        let mut progress = 2;
        while self.count.load(SeqCst) > 1
        {
            crucible_assume!(progress > 0);
            progress -= 1;
            let head1 = self.head.load(SeqCst);
            let next1 = self.array[head1 as usize].next.swap(-1, SeqCst);

            if next1 >= 0 {
                if let Ok(_) = self.head.compare_exchange(head1, next1, SeqCst, SeqCst) {
                    self.count.fetch_sub(1, SeqCst);
                    return head1;
                } else {
                    self.array[head1 as usize].next.swap(next1, SeqCst);
                }
            }
        }

        -1
    }

    fn push(&self, index:i32) {
        let mut head1 = self.head.load(SeqCst);

        loop {
            self.array[index as usize].next.store(head1, SeqCst);
            if let Err(new_head) = self.head.compare_exchange(head1, index, SeqCst, SeqCst) {
                head1 = new_head;
            } else {
                break;
            }

        }
        self.count.fetch_add(1, SeqCst);
    }

}

fn thd(stk: Arc<SafeStack>, arg: i32) {
    let x = stk.pop();
    if x >= 0 {
        stk.array[x as usize].value.store(arg, SeqCst);
        crucible_assert!(stk.array[x as usize].value.load(SeqCst) == arg);
        stk.push(x);
    }
}

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    let stk = Arc::new(SafeStack::new(3));

    for i in 0..3 {
        let stk_clone = Arc::clone(&stk);
        let _ = thread::spawn(move || {
            thd(stk_clone, i);
        });
    }

    // let stk_clone2 = Arc::clone(&stk);
    // let h2 = thread::spawn(move || {
    //     thd(stk_clone2, 1);
    // });

    // h1.join();
    // h2.join();
    // let v = Arc::new(vec![]);

    // for x in 0..1 {
    //     let my_v = Arc::clone(&v);
    //     let a = thread::spawn(move || {
    //         my_v[0].store(x, SeqCst);
    //     });
    // }
}
