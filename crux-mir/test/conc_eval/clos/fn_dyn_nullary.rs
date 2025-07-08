fn call_with_one(some_closure: &dyn Fn() -> i32) -> i32 {
    some_closure()
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = 123;
    call_with_one(&|| x + 123)
}

pub fn main() {
    println!("{:?}", crux_test());
}
