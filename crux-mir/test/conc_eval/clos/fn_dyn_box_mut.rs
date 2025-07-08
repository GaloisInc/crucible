fn call_closure_box(mut f: Box<dyn FnMut(i32, i32) -> i32>) -> i32 {
    let r = f(1, 2);
    // TODO: remove `forget` once `drop_in_place` works for `Box<dyn Trait>` (currently it enters
    // an infinite loop).
    std::mem::forget(f);
    r
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    call_closure_box(Box::new(|x, y| x + y))
}

pub fn main() {
    println!("{:?}", crux_test());
}
