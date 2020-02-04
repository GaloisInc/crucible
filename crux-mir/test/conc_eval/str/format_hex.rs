// FAIL: translation error with `slice.iter_mut().rev()`
#![feature(custom_attribute)]

#[crux_test]
fn crux_test() -> bool {
    let s = format!("a{:x}c", 123);
    &s == "a7bc"
}

pub fn main() {
    println!("{:?}", crux_test());
}
