// FAIL: fail or unimp constant: RealValRepr ConstFloat (FloatLit F64 "0f64")

fn f(x: (bool,bool)) -> bool {
    let y = 0.0;
    let s = "hello";
    // this is not actually an array literal
    let a = [0,1,2];
    // this is not actually a tuple literal
    let t = (0.1, 2);
    let (b,c) = t;
    y > 0.1 && s.len() > 3 && a.len() > 1 && c > 2
}

const ARG: (bool,bool) = (true, true);

#[cfg(with_main)]
fn main() {
    println!("{}", f(ARG))
}
