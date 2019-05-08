// FAIL: missing lifetime parameter in addAssign

fn f(_x: u8) -> i32 {
    let mut xs : [i32; 3] = [0; 3];
    xs[1] = 1;
    xs[2] = 2;
    let mut y : i32 = 0;
    for x in &xs {
        y += x;
    }
    y
}

const ARG: u8 = 42;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
