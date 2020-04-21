
#[cfg_attr(crux, crux_test)]
fn crux_test() -> usize {
    let xs = [1, 2, 3];

    let mut sum = 0;
    for x in xs.iter().cloned() {
        sum += x;
    }
    sum
}

pub fn main() {
    println!("{:?}", crux_test());
}
