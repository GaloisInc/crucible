use std::sync::Arc;

fn call_closure_arc(mut f: Arc<dyn Fn(i32, i32) -> i32>) -> i32 {
    let r = f(1, 2);
    r
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    call_closure_arc(Arc::new(|x, y| x + y))
}

pub fn main() {
    println!("{:?}", crux_test());
}
