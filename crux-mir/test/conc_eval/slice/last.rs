#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let arr = [1, 2, 3];
    // `.last` uses `from_end: true` indexing mode.
    *arr.last().unwrap()
}

pub fn main() {
    println!("{:?}", crux_test());
}
