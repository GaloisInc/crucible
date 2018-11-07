// This tests using polymorphic functions and parameterized data

pub fn f<T,U>(y : Result<T,U>) -> u32 {

    match y {
        Ok(x)  => 0,
        Err(_) => 1,
    } 
}

const ARG : Result<u32,u32> = Ok(0);


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
