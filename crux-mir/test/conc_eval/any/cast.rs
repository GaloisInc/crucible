use std::any::Any;

#[cfg_attr(crux, crux::test)]
fn cast_ref_through_any() {
    let value: u32 = 42;
    let any_ref: &dyn Any = &value;
    let recovered = any_ref.downcast_ref::<u32>().unwrap();
    assert_eq!(*recovered, 42);
}

#[cfg(with_main)] pub fn main() {
    println!("{:?}", cast_ref_through_any());
}
