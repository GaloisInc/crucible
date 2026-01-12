fn call_closure_box(f: Box<dyn FnOnce(i32, i32) -> i32>) -> i32 {
    f(1, 2)
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let z = 3_i32;
    call_closure_box(Box::new(move |x, y| x + y + z))
}

pub fn main() {
    println!("{:?}", crux_test());
}
