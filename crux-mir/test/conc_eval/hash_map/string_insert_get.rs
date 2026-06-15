use std::collections::HashMap;

const S1: &str = "long test string that will overflow the hasher buffer";
const S2: &str = "short";
const S3: &str = "other";


#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let mut m = HashMap::new();
    m.insert(S1.to_string(), 11);
    m.insert(S2.to_string(), 12);
    assert!(m.len() == 2);
    assert!(m.get(S3).is_none());
    (*m.get(S1).unwrap(), *m.get(S2).unwrap())
}

pub fn main() {
    println!("{:?}", crux_test());
}
