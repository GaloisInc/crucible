union U {
    x: u8,
    y: i8,
}

fn foo(b: bool) -> u8 {
    if b {
        let u = U { x: 42 };
        unsafe { u.x }
    } else {
        43
    }
}

#[cfg_attr(crux, crux::test)]
pub fn bar() -> u8 {
    foo(false)
}

pub fn main() {
    println!("{}", bar());
}
