// FAIL: can't unsize null pointers
use std::ptr;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> (bool, bool) {
    let p = &[1, 2] as *const [i32; 2] as *const [i32];
    let q = 0 as *const [i32; 2] as *const [i32];
    (p.is_null(), q.is_null())
}

pub fn main() {
    println!("{:?}", crux_test());
}
