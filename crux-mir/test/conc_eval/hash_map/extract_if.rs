use std::collections::HashMap;
use std::convert::TryInto;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> ([i32; 4], [i32; 4]) {
    let mut map: HashMap<i32, i32> = (0..8).map(|x| (x, x)).collect();
    let extracted: HashMap<i32, i32> = map.extract_if(|k, _v| k % 2 == 0).collect();
    let mut evens = extracted.keys().copied().collect::<Vec<_>>();
    let mut odds = map.keys().copied().collect::<Vec<_>>();
    evens.sort();
    odds.sort();
    (evens.try_into().unwrap(), odds.try_into().unwrap())
}

pub fn main() {
    println!("{:?}", crux_test());
}
