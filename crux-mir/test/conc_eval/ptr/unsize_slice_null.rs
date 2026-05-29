use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> bool {
    let p = 0 as *const [i32; 2] as *const [i32];
    p.is_null()
}

pub fn main() {
    println!("{:?}", crux_test());
}
