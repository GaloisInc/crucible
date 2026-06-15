use std::thread;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> bool {
    let t1 = thread::current();
    let t2 = thread::current();
    t1.id() == t2.id()
}

pub fn main() {
    println!("{:?}", crux_test());
}
