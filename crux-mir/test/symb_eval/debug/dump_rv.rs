extern crate crucible;
use crucible::{dump_rv, Symbolic};

struct S {
    x: u32,
    y: u32,
}

#[crux::test]
fn test() {
    dump_rv("a", (123, 456));
    let xy = <(u32, u32)>::symbolic_where("xy", |&(x, y)| x < 100 && y < 100);
    dump_rv("b", xy);
    dump_rv("c", S { x: xy.0, y: xy.1 });
}
