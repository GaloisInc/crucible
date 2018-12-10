// FAIL: Doesn't know about Option datatype
// This tests using polymorphic functions and parameterized data


pub fn g<T,U>(y : Result<T,U>) -> Option<T> {

    match y {
        Ok(x)  => Some(x),
        Err(_) => None,
    } 
}

fn f (x : u32) -> u32 {
    let z : Result<u32,u32> = Ok(x);
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
