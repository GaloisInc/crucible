#![feature(box_syntax)]

struct Test(i32);

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = box Test(1);
    x.0
}

pub fn main() {
    println!("{:?}", crux_test());
}
