


fn f (y:i32) -> i32 {

    let g = |x| x + y;

    g(1)

}

const ARG :i32 = 3;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
