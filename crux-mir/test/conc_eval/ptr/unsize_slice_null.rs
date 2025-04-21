// FAIL: can't unsize null pointers
use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> bool {
    // The unsize step fails because it uses an indexing operation to go from `*const [i32; 2]` to
    // `*const i32` (the data pointer of the resulting `*const [i32]`).
    let p = 0 as *const [i32; 2] as *const [i32];
    p.is_null()
}

pub fn main() {
    println!("{:?}", crux_test());
}
