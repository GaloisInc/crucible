
#[derive(Debug)]
struct MyStruct {
    x: u8,
    y: u8,
}

#[crux_test]
fn crux_test() -> bool {
    let s = format!("{:?}", MyStruct { x: 1, y: 2 });
    &s == "MyStruct { x: 1, y: 2 }"
}

pub fn main() {
    println!("{:?}", crux_test());
}
