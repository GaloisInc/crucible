//! A regression test for #1901.

#[derive(Clone, Copy)]
struct A(u32, u32);

#[repr(C)]
struct B {
    x: u32,
    y: [A; 3],
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let b = B {
        x: 1,
        y: [A(2, 2), A(3, 3), A(4, 4)],
    };
    let mut dest = [A(0, 0); 3];
    unsafe {
        std::ptr::copy(b.y.as_ptr(), dest.as_mut_ptr(), 3);
    }
    dest[1].1
}

pub fn main() {
    println!("{:?}", crux_test());
}
