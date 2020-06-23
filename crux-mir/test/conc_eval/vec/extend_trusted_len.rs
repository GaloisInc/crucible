use std::ptr;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> (i32, i32) {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.extend([10, 11].iter().cloned());
    (v[0], v[2])
}

pub fn main() {
    println!("{:?}", crux_test());
}
