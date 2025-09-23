// FAIL: attempt to mux differently-initialized unions

extern crate crucible;
use crucible::symbolic::Symbolic as _;

union U {
    x: u16,
    y: [u8; 2],
}

#[cfg_attr(crux, crux::test)]
fn foo() -> u16 {
    let x: u16 = 0x1234;
    let u = if bool::symbolic("cond") {
        U { x }
    } else {
        U { y: x.to_ne_bytes() }
    };
    x
}

fn main() {
    println!("{}", foo());
}
