use std::ops::Range;

fn f (x : i32) -> i32 {
    let y = Range { start: x, end: 10 } ;
    return y.end;
}

const ARG : i32 = 2;


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
