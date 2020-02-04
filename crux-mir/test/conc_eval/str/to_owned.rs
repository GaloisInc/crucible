#![feature(custom_attribute)]

#[crux_test]
fn crux_test() -> bool {
    let s = "aβc".to_owned();
    &s == "aβc"
}

pub fn main() {
    println!("{:?}", crux_test());
}
