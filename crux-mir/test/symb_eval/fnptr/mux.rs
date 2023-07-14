extern crate crucible;
use crucible::*;

fn f(x: i32) -> i32 {
    x + 1
}

fn g(x: i32) -> i32 {
    x - 1
}

#[crux::test]
fn crux_test() -> i32 {
    let b = bool::symbolic("cond");
    let p1: fn(i32) -> i32 = if b { f } else { g };
    let p2: fn(i32) -> i32 = if b { g } else { f };
    let x1 = p1(1);
    let x2 = p2(1);
    crucible_assert!(x1 == 0 || x1 == 2);
    crucible_assert!(x2 == 0 || x2 == 2);
    x1 + x2
}

pub fn main() {
    println!("{:?}", crux_test());
}
