fn f (x : u32) -> u32 {
    
    let mut k = 0;
    loop {
        if k == x {
            break;
        }
        k = k+1;
    }
    return k;
}

const ARG :u32 = 2;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
