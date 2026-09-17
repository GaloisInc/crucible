//! Check that `crucible-mir` correctly simulates `ptr::copy` when the source
//! and destination overlap.

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [u32; 5] {
    let mut a = [0, 1, 2, 3, 4];
    let src = a.as_mut_ptr();
    let dst = unsafe { src.add(1) };
    unsafe {
        std::ptr::copy(src, dst, 3);
    }
    a
}

pub fn main() {
    println!("{:?}", crux_test());
}
