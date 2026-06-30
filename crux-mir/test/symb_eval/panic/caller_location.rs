use std::panic::Location;

#[track_caller]
fn f() -> u32 {
    Location::caller().line()
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    f()
}

pub fn main() {
    println!("{:?}", crux_test());
}
