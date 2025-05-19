use std::convert::TryFrom;
extern crate crucible;
use crucible::*;

macro_rules! check {
    ($res:expr) => {
        if !$res.is_ok() {
            return None;
        }
    };
}

fn f() -> Option<u8> {
    let x_32 = u32::symbolic("x");
    check!(u8::try_from(x_32));
    let y_32 = u32::symbolic("y");
    crucible_assume!(y_32 < 256);
    check!(u8::try_from(y_32));
    Some(1)
}

#[crux::test]
fn crux_test() -> u8 {
    f().unwrap_or(0)
}
