use std::collections::HashMap;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut m = HashMap::new();
    m.insert(1, 11);
    m.insert(2, 12);
    m.remove(&1);
    assert!(m.len() == 1);
    assert!(m.get(&1).is_none());
    *m.get(&2).unwrap()
}

pub fn main() {
    println!("{:?}", crux_test());
}
