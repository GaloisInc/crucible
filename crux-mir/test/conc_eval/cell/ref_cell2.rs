// The `Drop` impl for the `RefMut` never runs, so the ref count is never reset, and the call to
// `borrow` fails.
use std::cell::RefCell;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = RefCell::new(1);
    {
        // Drop a tuple of Refs.  This requires handling tuple drop glue.
        let refs = (x.borrow(), x.borrow());
    }
    *x.borrow_mut() = 2;
    let val = *x.borrow();
    val
}

pub fn main() {
    println!("{:?}", crux_test());
}
