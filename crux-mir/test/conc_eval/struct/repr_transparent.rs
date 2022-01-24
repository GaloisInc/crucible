use std::mem;


#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
struct S((), [i32; 2], ());


#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let x = [3_i32; 2];
    // Construct repr(transparent) struct
    let s = S((), x, ());
    // Access field of repr(transparent) struct
    let y = s.1;
    assert!(x == y);

    // Transmute to and from repr(transparent)
    let s2: S = unsafe { mem::transmute(x) };
    assert!(s == s2);
    let y2: [i32; 2] = unsafe { mem::transmute(s2) };
    assert!(y == y2);

    // Cast raw pointers to and from repr(transparent)
    let p1: *const [i32; 2] = &s as *const S as *const [i32; 2];
    let p2: *const [i32; 2] = &x as *const [i32; 2];
    unsafe {
        assert!(*p1 == *p2);
        assert!(*(p1 as *const S) == *(p2 as *const S));
    }

    s.1[0] + x[0]
}

pub fn main() {
    println!("{:?}", crux_test());
}
