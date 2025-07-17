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
    let g: &dyn Fn() -> i32 = &f;
    let h: &dyn Fn() -> i32 = &make_i32;

    call_closure(g) + call_closure_once(g)
    // Calling `h` in particular tests that `transTerminatorKind`'s `Call`
    // behavior is amenable to non-`Constant`-shaped `TyFnDef` values, as `h` is
    // a `TyFnDef` and (at press time, anyway) is represented in MIR not as a
    // `Constant`.
    + call_closure(h) + call_closure_once(h)
}

pub fn main() {
    println!("{:?}", crux_test());
}
