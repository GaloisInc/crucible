// FAIL: Doesn't know about Option datatype
// This tests using polymorphic functions and parameterized data

pub fn g<T>(y : Option<T>) -> Option<T> {
    y
}

fn f (x : u32) -> u32 {
    let z : Option<u32> = Some(x);
    match g(z) {
        Some (y) => return y,
        None => return 0
    }
}

const ARG : u32 = 27;


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
