extern crate crucible;
use crucible::*;
use crucible::sym_bytes::SymBytes;

fn deserialize(b: &[u8]) -> (i16, i16) {
    match b[0] {
        0 => {
            let x = b[1] as i16 | (b[2] as i16) << 8;
            let y = b[3] as i16 | (b[4] as i16) << 8;
            (x, y)
        },
        1 => {
            let x = b[1] as i8 as i16;
            let y = b[2] as i8 as i16;
            (x, y)
        },
        2 => {
            let x = b[1] as i16 | (b[2] as i16) << 8;
            let y = x + (b[3] as i8 as i16);
            (x, y)
        },
        _ => panic!("bad encoding kind"),
    }
}

#[crux::test]
fn crux_test() -> i32 {
    let sym = SymBytes::symbolic("sym", 5);
    crucible_assume!(sym[0] <= 2);

    let (x, y) = deserialize(&sym);
    x as i32 + y as i32
}

pub fn main() {
    println!("{:?}", crux_test());
}
