
fn f(x: i32) -> i32 {
    x + 1
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let p: fn(i32) -> i32 = f;
    0
}

pub fn main() {
    println!("{:?}", crux_test());
}
