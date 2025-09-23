union U {
    x: u16,
    y: [u8; 2],
}

struct S {
    u: U,
}

fn foo(b: bool) -> u16 {
    if b {
        let u = U { x: 42 };
        let s = S { u };
        unsafe { s.u.x }
    } else {
        43
    }
}

#[cfg_attr(crux, crux::test)]
pub fn bar() -> u16 {
    foo(false)
}

pub fn main() {
    println!("{}", bar());
}
