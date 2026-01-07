//! Tests for concretization of `repr(transparent)` structs. The various
//! zero-sized types help exercise the pretty-printing logic that handles
//! extra/nested zero-sized values in `repr(transparent)` structs.

extern crate crucible;
use crucible::*;

use std::marker::PhantomData;

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct ZST0;

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct ZST1(());

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct ZST2<T>(T, [u8; 0]);

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct ZST3(ZST0, (ZST1, ZST2<ZST0>), PhantomData<[u8; 0]>);

#[derive(Debug)]
#[repr(transparent)]
struct STup(u16, ZST3);

#[derive(Debug)]
#[repr(transparent)]
struct SFld {
    x: u16,
    zs: ZST3,
}

#[derive(Debug)]
#[repr(transparent)]
enum ETup {
    X(ZST3, u16),
}

#[derive(Debug)]
#[repr(transparent)]
enum EFld {
    X { zs: ZST3, x: u16 },
}

#[crux::test]
fn crux_test() -> (STup, SFld, ETup, EFld, ZST3) {
    let x = u16::symbolic("x");

    let z0 = ZST0;
    let z1 = ZST1(());
    let z2 = ZST2(ZST0, []);
    let zs = ZST3(z0, (z1, z2), PhantomData);

    let st = STup(x, zs);
    let sf = SFld { x, zs };
    let et = ETup::X(zs, x);
    let ef = EFld::X { zs, x };

    crucible_assume!(x < 2);
    crucible_assume!(x > 0);

    concretize((st, sf, et, ef, zs))
}

pub fn main() {
    println!("{:?}", crux_test());
}
