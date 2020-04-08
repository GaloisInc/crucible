extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut result = 0;
    let one = 1;
    if bool::symbolic("cond") {
        let r = &one;
        let r2 = &r;
        result = **r2;
    }
    result
}

pub fn main() {
    println!("{:?}", crux_test());
}

