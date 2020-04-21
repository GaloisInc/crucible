#![cfg_attr(not(with_main), no_std)]

fn f(_: ()) -> i32 {
    let x = Some(1);
    let mut y = Some(2);

    let mut acc = 0;
    if let Some(ref x) = x {
        acc += *x;
    }
    if let Some(ref mut y) = y {
        *y += 1;
    }
    if let Some(ref mut y) = y {
        acc += *y;
    }

    acc
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> i32 { f(ARG) }
