pub trait T {
    fn def () -> Self;
}

pub trait U<Rhs: ?Sized=Self> {
    fn bin(&self,other: &Rhs) -> bool;
}


impl T for i32 {
    fn def () -> i32 { 25 }
}

impl U<i32> for i32 {
    fn bin(&self,other:&Self) -> bool { *self == *other }
}


fn f(x : i32) -> i32 {
    if x.bin(&x) {
        i32::def()
    } else {
        33
    }
}

const ARG: i32 = 12;

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
