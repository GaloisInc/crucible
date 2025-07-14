extern crate crucible;
use crucible::{print_str, Symbolic};

#[crux::test]
fn test() {
    print_str("hello");
    let b = bool::symbolic("b");
    if b {
        print_str("foo");
    } else {
        print_str("bar");
    }
}
