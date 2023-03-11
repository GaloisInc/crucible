/// Drop a `Vec<T>` where `T: Drop`.  This triggers a call to `drop_in_place::<[T]>`, which uses a
/// few operations that aren't seen in other drop glues.

struct S(i32);

impl Drop for S {
    fn drop(&mut self) {
        // No-op
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let v = vec![S(1), S(2), S(3)];
    drop(v);
}

pub fn main() {
    println!("{:?}", crux_test());
}
