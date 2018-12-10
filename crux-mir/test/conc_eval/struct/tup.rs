// FAIL: Printing of unit constructor not correct yet
fn g () -> char {
    '\x00'
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
