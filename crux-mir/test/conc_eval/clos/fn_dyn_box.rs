// FAIL: standalone use of `dyn` in the receiver of `call_once`
fn call_closure_box(f: Box<dyn FnOnce(i32, i32) -> i32>) -> i32 {
    f(1, 2)
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    call_closure_box(Box::new(|x, y| x + y))
}

pub fn main() {
    println!("{:?}", crux_test());
}
