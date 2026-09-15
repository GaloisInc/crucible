// FAIL: non-integer peelIndex
//
// `ptr::copy` dispatches to `intrinsics::copy`, which calls `mirRef_peelIndex` on the `src`
// pointer.  This tries to convert the offset of the `AgOffset_RefPath` to an index by dividing it
// by the element size, failing if this would produce a non-integer index.  This can fail in
// practice if the element type has size strictly greater than alignment, like in this case where
// type `A` has size 8, alignment 4, and the offset of the pointer is 4 (a multiple of the
// alignment but not of the size).

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
        std::ptr::copy(&b.y[0], &mut dest[0], 3);
    }
    dest[1].1
}

pub fn main() {
    println!("{:?}", crux_test());
}
