use std::ffi::CStr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    let s1 = CStr::from_bytes_with_nul(b"123\0").unwrap();
    let s2 = CStr::from_bytes_with_nul(
        b"very long string in case there are heuristics in memchr that care about the input size\0",
    ).unwrap();
    s1.to_bytes().len() + s2.to_bytes().len()
}

pub fn main() {
    println!("{:?}", crux_test());
}
