
#[crux_test]
fn crux_test() -> bool {
    let s = format!("{:?}", [1,2,3,4]);
    &s == "[1, 2, 3, 4]"
}

pub fn main() {
    println!("{:?}", crux_test());
}
