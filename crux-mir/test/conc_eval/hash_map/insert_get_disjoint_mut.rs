use std::collections::HashMap;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let mut m = HashMap::new();
    m.insert(1, 11);
    m.insert(2, 12);
    m.insert(3, 13);
    m.insert(4, 14);
    let [r3, r1, r5] = m.get_disjoint_mut([&3, &1, &5]);
    let r3 = r3.unwrap();
    let r1 = r1.unwrap();
    assert!(*r3 == 13);
    assert!(*r1 == 11);
    assert!(r5 == None);
    *r3 = 23;
    *r1 = 21;
    (*m.get(&3).unwrap(), *m.get(&1).unwrap())
}

pub fn main() {
    println!("{:?}", crux_test());
}
