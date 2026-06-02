// FAIL: attempt to mux differently-initialized unions

extern crate crucible;
use crucible::{crucible_assert, dump_rv, Symbolic as _};

#[repr(C)]
#[derive(Clone, Copy)]
struct S(u8);

#[repr(C)]
#[derive(Clone, Copy)]
struct X {
    a: S,
    b: S,
}

#[derive(Clone, Copy)]
union U {
    x: X,
    y: [u8; 2],
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x: X = X { a: S(42), b: S(84) };
    let c = bool::symbolic("cond");
    let u = if c { U { x } } else { U { y: [x.b.0, x.a.0] } };

    dump_rv("u", u.clone());

    let first = unsafe { *(&raw const u as *const u8) };
    if c {
        crucible_assert!(first == 42);
    } else {
        crucible_assert!(first == 84);
    }
}

fn main() {
    println!("{:?}", crux_test());
}
