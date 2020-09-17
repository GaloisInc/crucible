use std::collections::VecDeque;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> [i32; 2] {
    let mut v: VecDeque<_> = vec![1, 2, 3, 4, 5].into();
    v.retain(|&x| x % 3 == 1);
    assert!(v.len() == 2);
    [v[0], v[1]]
}

pub fn main() {
    println!("{:?}", crux_test());
}
