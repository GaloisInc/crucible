use std::collections::HashMap;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut m = HashMap::new();
    m.insert(1, 11);
    m.insert(1, 100);
    m.insert(2, 12);
    assert!(m.len() == 2);
    *m.get(&1).unwrap()
}

pub fn main() {
    println!("{:?}", crux_test());
}
