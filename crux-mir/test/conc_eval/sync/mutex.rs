use std::sync::Mutex;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let m = Mutex::new(1);
    let x = *m.lock().unwrap();
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
