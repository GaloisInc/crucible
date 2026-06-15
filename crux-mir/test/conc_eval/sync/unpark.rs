use std::thread;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    thread::current().unpark();
    1
}

pub fn main() {
    println!("{:?}", crux_test());
}
