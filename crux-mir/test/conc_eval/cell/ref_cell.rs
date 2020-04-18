// FAIL: requires Drop support
// The `Drop` impl for the `RefMut` never runs, so the ref count is never reset, and the call to
// `borrow` fails.
use std::cell::RefCell;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let x = RefCell::new(1);
    *x.borrow_mut() = 2;
    let val = *x.borrow();
    val
}

pub fn main() {
    println!("{:?}", crux_test());
}
