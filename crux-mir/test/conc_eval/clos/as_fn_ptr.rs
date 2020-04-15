// FAIL: ClosureFnPointer cast

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    // The closure's `Fn::call` impl takes the closure environment as an argument, but the function
    // pointer takes no arguments.  Performing this conversion requires either generating a custom
    // shim or special-casing empty closures to omit the env argument.  (rustc_codegen_ssa does the
    // latter.)
    let f = (|| 1) as fn() -> i32;
    f()
}

pub fn main() {
    println!("{:?}", crux_test());
}
