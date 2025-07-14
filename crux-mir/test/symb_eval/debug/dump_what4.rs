extern crate crucible;
use crucible::{dump_what4, Symbolic};

#[crux::test]
fn test() {
    dump_what4("a", 123);
    let x = u32::symbolic_where("x", |&x| x < 100);
    dump_what4("b", x + 1);
    dump_what4("c", x == 0);
}
