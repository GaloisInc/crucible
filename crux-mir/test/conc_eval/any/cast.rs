use std::any::Any;
use std::marker::PhantomData;

fn cast_ref_through_any() {
    let value: u32 = 42;
    let any_ref: &dyn Any = &value;
    let recovered = any_ref.downcast_ref::<u32>().unwrap();
    assert_eq!(*recovered, 42);
}

fn cast_ref_through_any_can_fail() {
    let value: u32 = 42;
    let any_ref: &dyn Any = &value;
    let recovered = any_ref.downcast_ref::<u64>();
    assert!(recovered.is_none());
}

struct T<A>{
    phantom: PhantomData<A>
}

fn casts_empties_use_substs() {
    let value: T<u8> = T::<u8>{ phantom: PhantomData };
    let any_ref: &dyn Any = &value;
    assert!(any_ref.downcast_ref::<T<u8>>().is_some());
    assert!(any_ref.downcast_ref::<T<u16>>().is_none());
}

#[cfg(not(with_main))]
#[cfg_attr(crux, crux::test)]
fn crux_test() {
    cast_ref_through_any();
    cast_ref_through_any_can_fail();
    casts_empties_use_substs();
}

#[cfg(with_main)] pub fn main() {
    cast_ref_through_any_can_fail();
    cast_ref_through_any();
    casts_empties_use_substs();
    println!("()");
}
