use std::collections::VecDeque;

#[crux_test]
fn crux_test() -> [i32; 5] {
    let mut v: VecDeque<_> = vec![1, 2, 3, 4, 5].into();
    [
        v.pop_back().unwrap(),
        v.pop_back().unwrap(),
        v.pop_back().unwrap(),
        v.pop_front().unwrap(),
        v.pop_back().unwrap(),
    ]
}

pub fn main() {
    println!("{:?}", crux_test());
}
