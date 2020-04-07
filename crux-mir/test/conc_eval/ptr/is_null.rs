use std::ptr;

#[crux_test]
fn crux_test() -> (bool, bool) {
    let p = &1 as *const i32;
    let q = 0 as *const i32;
    (p.is_null(), q.is_null())
}

pub fn main() {
    println!("{:?}", crux_test());
}
