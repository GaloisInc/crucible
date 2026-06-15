use std::thread;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    thread::current().unpark();
    // Since we called `unpark`, this call to `park` shouldn't block.
    thread::park();
    1
}

pub fn main() {
    println!("{:?}", crux_test());
}
