// Test that calling `Box<dyn FnOnce>` works even when the erased type is not a closure but
// something else (in this case, `Box<F>`).
fn call_closure_box(f: Box<dyn FnOnce(i32, i32) -> i32>) -> i32 {
    f(1, 2)
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let z = 3_i32;
    let f = Box::new(move |x, y| x + y + z);
    call_closure_box(Box::new(f))
}

pub fn main() {
    println!("{:?}", crux_test());
}
