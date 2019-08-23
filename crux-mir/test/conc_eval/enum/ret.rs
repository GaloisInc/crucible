#![cfg_attr(not(with_main), no_std)]
#[derive(Debug)]
enum E {
    A(u8),
    B(i32),
}

// don't derive Debug unless we need it for main
#[cfg(not(with_main))]
enum E {
    A(u8),
    B(i32),
}

fn f(_: ()) -> E {
    E::A(42)
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] pub fn main() { f(ARG); }
