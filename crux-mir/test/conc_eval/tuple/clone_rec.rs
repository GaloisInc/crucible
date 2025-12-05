// Guard the call to clone() behind an intermediate function to reduce the
// likelihood that rustc optimizes away the call to clone().
#[inline(never)]
fn my_clone<T: Clone>(x: &T) -> T {
    x.clone()
}

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let x = (1, (2, (3, 4)));
    let y = my_clone(&x);
    assert!(x == y);
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
