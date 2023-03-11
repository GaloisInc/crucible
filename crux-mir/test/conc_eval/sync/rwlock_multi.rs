use std::sync::RwLock;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let m = RwLock::new(1);
    {
        let mut g = m.write().unwrap();
        assert!(m.try_write().is_err());
        assert!(m.try_read().is_err());
        *g += 1;
    }
    {
        let mut g = m.write().unwrap();
        *g += 1;
    }
    let x = *m.read().unwrap();
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
