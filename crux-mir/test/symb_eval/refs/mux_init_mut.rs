extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> i32 {
    let mut result = 0;
    if bool::symbolic("cond") {
        let mut r = &mut result;
        let r2 = &mut r;
        **r2 = 1;
    }
    result
}

pub fn main() {
    println!("{:?}", crux_test());
}

