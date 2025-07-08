fn call_closure_box(mut f: Box<dyn FnMut(i32, i32) -> i32>) -> i32 {
    let r = f(1, 2);
    r
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    call_closure_box(Box::new(|x, y| x + y))
}

pub fn main() {
    println!("{:?}", crux_test());
}
