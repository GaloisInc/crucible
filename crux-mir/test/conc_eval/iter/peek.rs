
#[cfg_attr(crux, crux_test)]
fn crux_test() -> usize {
    let xs = [1, 2, 3];

    let mut sum = 0;
    let mut it = xs.iter().peekable();
    while it.peek().map_or(false, |&&x| x < 3) {
        sum += it.next().unwrap();
    }
    sum
}

pub fn main() {
    println!("{:?}", crux_test());
}
