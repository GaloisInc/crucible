extern crate crucible;
use crucible::*;

#[derive(Clone, Copy)]
#[repr(C)]
struct P {
    a: u8,
    b: i64,
}

#[crux::test]
fn struct_array_sym_index() {
    let mut arr = [P { a: 1, b: 2 }, P { a: 3, b: 4 }];
    let i = usize::symbolic("i");
    crucible_assume!(i < 2);
    let p = arr[i];
    crucible_assert!(p.a as i64 + 1 == p.b);

    arr[i] = P { a: 5, b: 6 };
    let p = arr[i];
    crucible_assert!(p.a as i64 + 1 == p.b);
}

#[crux::test]
fn tuple_array_sym_index() {
    let mut arr: [(u16, u32); 2] = [(1, 2), (3, 4)];
    let i = usize::symbolic("i");
    crucible_assume!(i < 2);
    let t = arr[i];
    crucible_assert!(t.0 as u32 + 1 == t.1);

    arr[i] = (5, 6);
    let t = arr[i];
    crucible_assert!(t.0 as u32 + 1 == t.1);
}
