

fn g () -> char {
    'a'
}

fn h () -> () {
    ()
}

fn f (x : i32) -> () {
    h ();
}

const ARG : i32 = 0;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
