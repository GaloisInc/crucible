use std::sync::RwLock;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let m = RwLock::new(1);
    *m.write().unwrap() = 2;
    let x = *m.read().unwrap();
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
