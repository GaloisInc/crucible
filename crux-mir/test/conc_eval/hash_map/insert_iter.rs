use std::collections::HashMap;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [i32; 2] {
    let mut m = HashMap::new();
    m.insert(1, 11);
    m.insert(2, 12);
    assert!(m.iter().count() == 2);
    let mut out = [0; 2];
    for (&k, &v) in m.iter() {
        out[k as usize - 1] = v;
    }
    out
}

pub fn main() {
    println!("{:?}", crux_test());
}
