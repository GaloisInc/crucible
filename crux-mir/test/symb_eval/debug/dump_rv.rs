extern crate crucible;
use crucible::{dump_rv, Symbolic};
use crucible::alloc::reallocate;
use crucible::array::Array;

struct S {
    x: u32,
    y: u32,
}

#[crux::test]
fn test() {
    dump_rv("a", (123, 456));
    let xy = <(u32, u32)>::symbolic_where("xy", |&(x, y)| x < 100 && y < 100);
    dump_rv("b", xy);
    dump_rv("c", S { x: xy.0, y: xy.1 });

    let mut v = [0u8, 1u8];
    dump_rv("d", v);
    let mut vp = v.as_mut_ptr();
    crucible::alloc::reallocate(vp, 5);
    unsafe {
        *vp.offset(2) = 42;
        if v[0] == 0 {
            *vp.offset(3) = 27;
        }
    }
    crucible::dump_rv("e", v);

    let mut arr = Array::<u8>::zeroed();
    arr = arr.update(2, 42);
    arr = arr.update(3, 27);
    crucible::dump_rv("f", arr);
}
