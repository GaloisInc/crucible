#![cfg_attr(not(with_main), no_std)]
trait F : Sized {
    
    type Output : Sized;
    fn ff(self) -> Self::Output; 
    
}

impl F for [u8;5] {
    type Output = u8;
    fn ff(self) -> Self::Output {
        self[0]
    }
}

fn g<A:F,B:F>(a:A,b:B) -> u8 {
    a.ff();
    b.ff();
    0
}


fn f (x:u8) -> u8 {
    let xs = [x;5];
    g(xs,xs)

}


const ARG: u8 = 23;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u8 { f(ARG) }
