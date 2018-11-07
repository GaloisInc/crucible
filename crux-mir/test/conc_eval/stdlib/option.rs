
fn f (y : u32) -> bool { 
    let x: Option<u32> = Some(y);
    return x.is_some() == true;
}

const ARG: u32 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
