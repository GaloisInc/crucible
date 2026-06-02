use std::mem::transmute;

#[repr(C)]
#[derive(Clone)]
struct A(u8);

#[repr(C)]
#[derive(Clone)]
struct B {
    b: u8,
}

#[repr(C)]
#[derive(Clone)]
struct CD {
    c: u8,
    d: u8,
}

#[repr(transparent)]
#[derive(Clone)]
struct E {
    e: u8,
}

#[repr(C)]
#[derive(Clone)]
struct S {
    a: A,
    b: B,
    cd: CD,
    e: E,
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let a = 97;
    let b = 98;
    let c = 99;
    let d = 100;
    let e = 101;

    let s = S {
        a: A(a),
        b: B { b },
        cd: CD { c, d },
        e: E { e },
    };

    assert_eq!(s.a.0, a);
    assert_eq!(s.b.b, b);
    assert_eq!(s.cd.c, c);
    assert_eq!(s.cd.d, d);
    assert_eq!(s.e.e, e);

    let arr8: [u8; 5] = unsafe { transmute(s.clone()) };
    assert_eq!(arr8[0], s.a.0);
    assert_eq!(arr8[1], s.b.b);
    assert_eq!(arr8[2], s.cd.c);
    assert_eq!(arr8[3], s.cd.d);
    assert_eq!(arr8[4], s.e.e);

    let r#str0 = unsafe { str::from_utf8_unchecked(&arr8) };
    let r#str1 = unsafe { str::from_utf8_unchecked(&arr8[1..]) };
    assert_eq!(r#str0, "abcde");
    assert_eq!(r#str1, "bcde");
}

fn main() {
    println!("{:?}", crux_test());
}
