union U {
    x: u8,
    y: i8,
}

pub static FOO: U = U { x: 42 };

fn foo(b: bool) -> u8 {
    if b {
        // Note that it doesn't suffice to merely have a `static` union value
        // declaration; if no function refers to the value, dead-code
        // elimination seems to get rid of it.
        unsafe { FOO.x }
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
