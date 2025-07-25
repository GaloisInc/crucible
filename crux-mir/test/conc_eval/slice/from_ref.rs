use std::cell::Cell;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    // We want to check that our override of `crucible_slice_from_ref_hook`
    // properly aliases its input and output. We do so by making the conversion
    // source mutable via `Cell`, and checking that writes to that source can be
    // observed by reading the conversion target, and vice versa.
    let foo: Cell<i32> = Cell::new(42);
    let foo_slice: &[Cell<i32>] = core::slice::from_ref(&foo);

    foo.set(43);
    assert_eq!(foo_slice[0].get(), 43);

    foo_slice[0].set(44);
    assert_eq!(foo.get(), 44);

    foo.into_inner()
}

fn main() {
    println!("{:?}", crux_test());
}
