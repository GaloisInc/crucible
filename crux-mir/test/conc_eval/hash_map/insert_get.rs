use std::collections::HashMap;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let mut m = HashMap::new();
    m.insert(1, 11);
    m.insert(2, 12);
    assert!(m.len() == 2);
    assert!(m.get(&3).is_none());
    (*m.get(&1).unwrap(), *m.get(&2).unwrap())
}

pub fn main() {
    println!("{:?}", crux_test());
}
