use std::collections::VecDeque;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> [i32; 5] {
    let mut v: VecDeque<_> = vec![1, 2, 3, 4, 5].into();
    let mut it = v.iter();
    let a = *it.next().unwrap();
    let mut it2 = it.clone();
    [
        a,
        *it.next().unwrap(),
        *it.next().unwrap(),
        *it2.next().unwrap(),
        *it2.next().unwrap(),
    ]
}

pub fn main() {
    println!("{:?}", crux_test());
}
