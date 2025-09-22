// This currently passes, but will likely fail in the future if/when Crucible
// takes layout information into account when computing union representations
// and/or converting between fields, on account of the difference in size and
// alignment between `Small` and `Large`.

#[derive(Clone, Copy)]
enum Small {
    X(u16),
}

#[derive(Clone, Copy)]
#[repr(align(8))]
enum Large {
    Y(u16),
}

union U {
    small: Small,
    large: Large,
}

#[cfg_attr(crux, crux::test)]
fn foo() -> u16 {
    let x: u16 = 0x1234;
    let small = Small::X(x);
    let u: U = U { small };

    let Large::Y(y) = unsafe { u.large };
    assert_eq!(x, y);
    y
}

fn main() {
    println!("{:?}", foo());
}
