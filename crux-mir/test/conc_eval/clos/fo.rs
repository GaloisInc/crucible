
#![feature(type_ascription)]

fn f (y:i32) -> i32 {
    let z = 12;
    let w = 13;
    
    let g = |x:i32| x + y + z + w;

    g((1 :i32))

}

const ARG :i32 = 3;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
