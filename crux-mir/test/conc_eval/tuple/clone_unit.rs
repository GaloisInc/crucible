//! Test that the clone shim generated for unit values is appropriately typed.
//! All we really want to do is clone `()` - we only use the generalized
//! `my_clone`, rather than e.g. `().clone()`, to ensure rustc doesn't optimize
//! out the faulty clone shim.

#[inline(never)]
fn my_clone<T: Clone>(x: &T) -> T {
    x.clone()
}

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let x = ();
    let y = my_clone(&x);
    assert!(x == y);
}

fn main() {
    println!("{:?}", f());
}
