extern crate crucible;
extern crate crucible_proc_macros;

use crucible::*;
use crucible_proc_macros::Symbolic;

#[derive(Symbolic)]
struct Unit;

#[derive(Symbolic)]
struct NamedFields {
    field1: u32,
    field2: u64,
}

#[derive(Symbolic)]
struct TupleStruct(bool);

#[derive(Symbolic)]
enum Empty {}

#[derive(Symbolic)]
enum NonEmpty {
    A,
    B(u8),
    C(u16, u32),
    D { x: i32, y: i16 },
}

#[derive(Symbolic)]
struct Pair<A, B> {
    fst: A,
    snd: B,
}

#[crux::test]
fn empty() {
    let x = <Empty>::symbolic("");
    crucible_assert!(false); // should be unreachable!
}

#[crux::test]
fn nonempty() {
    <Unit>::symbolic("");
    <NamedFields>::symbolic("");
    <TupleStruct>::symbolic("");
    <NonEmpty>::symbolic("");
    <Pair<bool, bool>>::symbolic("");
}
