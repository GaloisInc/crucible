// FAIL: `Rc` uses standard (untyped) allocation functions
use std::rc::Rc;

fn call_closure_rc(mut f: Rc<dyn Fn(i32, i32) -> i32>) -> i32 {
    let r = f(1, 2);
    r
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    call_closure_rc(Rc::new(|x, y| x + y))
}

pub fn main() {
    println!("{:?}", crux_test());
}
