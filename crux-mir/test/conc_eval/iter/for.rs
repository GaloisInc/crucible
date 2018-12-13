fn f (mut x : u32) -> u32 {

    for k in 0 .. 10 {
        x = x + k;
    }

    return x;
}


const ARG :u32 = 2;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
