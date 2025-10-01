fn foo() -> u8 { return 42; }

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u8 {
    let fn_ptr_safe: fn() -> u8 = foo;
    let fn_ptr_unsafe: unsafe fn() -> u8 = fn_ptr_safe;
    unsafe { fn_ptr_unsafe() }
}

fn main() {
    println!("{:?}", crux_test());
}