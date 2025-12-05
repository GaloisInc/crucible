// FAIL: `Rc` uses `mem::align_of_val`
use std::rc::Rc;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = Rc::new(123);
    *x
}

pub fn main() {
    println!("{:?}", crux_test());
}
