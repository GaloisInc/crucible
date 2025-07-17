fn make_i32() -> i32 {
    42
}

fn call_closure<F: Fn() -> i32>(f: F) -> i32 {
    f()
}

fn call_closure_once<F: FnOnce() -> i32>(f: F) -> i32 {
    f()
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let f: fn() -> i32 = make_i32;
    // By passing `f`, a function pointer, we're ensuring that `call_closure`
    // can interact with function _pointer_ shims in particular. It does not
    // suffice to pass `make_i32` directly, as this resolves to a function
    // item type, rather than a function pointer.
    call_closure(f) + call_closure_once(f)
}

pub fn main() {
    println!("{:?}", crux_test());
}
