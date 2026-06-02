extern crate crucible;
use crucible::dump_rv;

#[repr(C)]
struct W {
    w: u8,
}

#[repr(C)]
struct X(u16);

#[repr(C)]
struct YZ {
    y: u32,
    z: u32,
}

#[repr(C)]
struct S {
    w: W,
    x: X,
    yz: YZ,
}

#[crux::test]
fn test() {
    // Note that the expected output for this may change if Rust changes the
    // algorithm it uses to lay out tuples. However, the expected output should
    // still reflect a flat, non-nested `MirAggregate`.
    let nested_tuple = (((1u8, 2u16), 3u32, (4u64,), 5i8), (6i16, (7i32, 8i64)));
    dump_rv("nested_tuple", nested_tuple);

    // `nested_array`'s output should reflect a flattened aggregate.
    let nested_array = [[1u16, 2], [3, 4]];
    dump_rv("nested_array", nested_array);

    // Dumping `slice` and `slice_head` shows that the `RegValue`s for both of
    // them consist of precisely one use of `AgOffset_RefPath`, combining the
    // two offsets involved in the `[1][1..]` indexing operation, rather than
    // two separate `AgOffset`s.
    let slice: &[u16] = &nested_array[1][1..];
    dump_rv("slice", slice);
    dump_rv("slice head", &slice[0]);

    // `nested_struct`'s output should reflect a flattened aggregate.
    let nested_struct = S {
        w: W { w: 23 },
        x: X(24),
        yz: YZ { y: 25, z: 26 },
    };
    dump_rv("nested_struct", nested_struct);
}
