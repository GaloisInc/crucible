use std::sync::Mutex;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let m = Mutex::new(1);
    {
        let mut g = m.lock().unwrap();
        assert!(m.try_lock().is_err());
        *g += 1;
    }
    {
        let mut g = m.lock().unwrap();
        *g += 1;
    }
    let x = *m.lock().unwrap();
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
