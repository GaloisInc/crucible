#[cfg(with_main)]
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
fn main() {
    println!("{:?}", f(ARG))
}
