extern crate crucible;
extern crate crucible_proc_macros;

use alloc::string::String;
use alloc::vec::Vec;
use crucible::{crucible_assert, BoundedSymbolic, Symbolic};
use crucible_proc_macros::{BoundedSymbolic, Symbolic};

#[derive(Symbolic)]
struct Unit;

#[derive(BoundedSymbolic)]
struct NamedFields {
    field1: u32,
    field2: u64,
}

#[derive(BoundedSymbolic)]
struct TupleStruct(bool);

#[derive(BoundedSymbolic)]
struct Pair<A, B> {
    fst: A,
    snd: B,
}

#[derive(BoundedSymbolic)]
struct MixedStruct {
    a: [u8; 10],
    x: u16,
    #[bounded]
    v: Vec<u8>,
    #[bounded]
    s: String,
    u: Unit,
}

#[derive(BoundedSymbolic)]
enum Empty {}

#[derive(BoundedSymbolic)]
enum NonEmpty {
    A,
    B(u8),
    C(u16, u32),
    D { x: i32, y: i16 },
    E([u8; 10]),
    F(#[bounded] Vec<u8>),
    G(#[bounded] String),
    H(Unit),
}

#[crux::test]
fn empty() {
    let _x = <Empty>::bounded_symbolic::<0>("");
    crucible_assert!(false); // should be unreachable!
}

#[crux::test]
fn nonempty() {
    const N: usize = 3;
    <NamedFields>::bounded_symbolic::<N>("");
    <TupleStruct>::bounded_symbolic::<N>("");
    <Pair<bool, bool>>::bounded_symbolic::<N>("");

    let mixed = MixedStruct::bounded_symbolic::<N>("");
    crucible_assert!(mixed.v.len() <= N);
    crucible_assert!(mixed.s.len() <= N);

    let non_empty = <NonEmpty>::bounded_symbolic::<N>("");
    match non_empty {
        NonEmpty::F(v) => crucible_assert!(v.len() <= N),
        NonEmpty::G(s) => crucible_assert!(s.len() <= N),
        _ => crucible_assert!(true),
    }
}
