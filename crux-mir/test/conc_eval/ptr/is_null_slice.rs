use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (bool, bool) {
    let p = &[1, 2] as *const [i32; 2] as *const [i32];
    let q = ptr::slice_from_raw_parts(0 as *const i32, 0);
    (p.is_null(), q.is_null())
}

pub fn main() {
    println!("{:?}", crux_test());
}
