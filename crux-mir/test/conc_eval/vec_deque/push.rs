use std::collections::VecDeque;

#[crux_test]
fn crux_test() -> [i32; 5] {
    let mut v = VecDeque::new();
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    v.push_front(4);
    v.push_back(5);
    [v[0], v[1], v[2], v[3], v[4]]
}

pub fn main() {
    println!("{:?}", crux_test());
}
