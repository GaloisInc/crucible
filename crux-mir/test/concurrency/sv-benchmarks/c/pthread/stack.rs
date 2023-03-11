extern crate crucible;

use crucible::*;
use std::thread;
use std::sync::{Arc,Mutex};

const SIZE: usize = 5;

struct Stack {
    top: usize,
    arr: [u32; SIZE],
    flag: bool,
}

impl Stack {
    fn new() -> Stack {
        Stack {
            top: 0,
            arr: [0; SIZE],
            flag: false,
        }
    }
    fn inc_top(&mut self) {
        self.top += 1;
    }
    fn dec_top(&mut self) {
        self.top -= 1;
    }
    fn get_top(&self) -> usize {
        self.top
    }
    fn empty(&self) -> bool {
        self.top == 0
    }
    fn push(&mut self, val:u32) -> bool
    {
        if self.top == self.arr.len() {
            false
        } else {
            self.arr[self.get_top()] = val;
            self.inc_top();
            true
        }
    }
    fn pop(&mut self) -> Option<u32>
    {
        if self.top == 0 {
            None
        } else {
            self.dec_top();
            Some(self.arr[self.get_top()])
        }
    }
}

fn t1(stack: Arc<Mutex<Stack>>, with_flag: bool)
{
    for i in 0..SIZE {
        let mut pstack = stack.lock().unwrap();

        let tmp = u32::symbolic("tmp");
        crucible_assume!((tmp as usize) < SIZE);

        let push_ok = pstack.push(tmp);
        crucible_assert!(push_ok);

        if (with_flag) {
            pstack.flag = true;
        }
        stack.crucible_TEMP_unlock();
    }
}

fn t2(stack: Arc<Mutex<Stack>>, with_flag: bool)
{
    for i in 0..SIZE {
        let mut pstack = stack.lock().unwrap();

        if (with_flag && pstack.flag) || pstack.top > 0 {
            let popped = pstack.pop();
            crucible_assert!(popped != None);
        }

        stack.crucible_TEMP_unlock();
    }
}

#[cfg_attr(crux, crux::test)]
fn stack_1()
{
    let stk = Arc::new(Mutex::new(Stack::new()));

    let pstk1 = Arc::clone(&stk);
    let pstk2 = Arc::clone(&stk);

    let h1 = thread::spawn(move || t1(pstk1, false));
    let h2 = thread::spawn(move || t2(pstk2, false));

    h1.join();
    h2.join();
}

#[cfg_attr(crux, crux::test)]
fn stack_2()
{
    let stk = Arc::new(Mutex::new(Stack::new()));

    let pstk1 = Arc::clone(&stk);
    let pstk2 = Arc::clone(&stk);

    let h1 = thread::spawn(move || t1(pstk1, true));
    let h2 = thread::spawn(move || t2(pstk2, true));

    h1.join();
    h2.join();
}
