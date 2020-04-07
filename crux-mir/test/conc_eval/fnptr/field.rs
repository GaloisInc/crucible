
fn test_func(x: i32) -> i32 {
    x + 1
}

struct Test {
    f: fn(i32) -> i32,
}

#[crux_test]
fn crux_test() -> i32 {
    let f = Test { f: test_func };
    (f.f)(1)
}

pub fn main() {
    println!("{:?}", crux_test());
}
