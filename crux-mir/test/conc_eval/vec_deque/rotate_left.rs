use std::collections::VecDeque;

#[crux_test]
fn crux_test() -> [i32; 5] {
    let mut v: VecDeque<_> = vec![1, 2, 3, 4, 5].into();
    v.rotate_left(2);
    [v[0], v[1], v[2], v[3], v[4]]
}

pub fn main() {
    println!("{:?}", crux_test());
}
