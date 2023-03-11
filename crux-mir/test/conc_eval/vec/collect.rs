#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let xs = (0..10).collect::<Vec<_>>();
    let mut sum = 0;
    for x in xs {
        sum += x;
    }
    sum
}

pub fn main() {
    println!("{:?}", crux_test());
}
