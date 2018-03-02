#[cfg(with_main)]
#[derive(Debug)]
struct S {
    x: u8,
    y: i32,
}

// don't derive Debug unless we need it for main
#[cfg(not(with_main))]
struct S {
    x: u8,
    y: i32,
}

fn f(_: ()) -> u8 {
    let s = S { x: 42, y: 120 };
    s.x
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
