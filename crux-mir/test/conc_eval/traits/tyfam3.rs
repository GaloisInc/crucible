// FAIL: needs a polymorphic member in trait dictionary

// 0 /= 1, i.e. not all types are instantiated during dictionary creation

trait F : Sized {
    
    type Output : Sized;
    fn ff(self) -> Self::Output; 
    
}

trait G {
    fn g<B:F>(&self,b:B) -> B::Output;
}

impl F for [u8;5] {
    type Output = u8;
    fn ff(self) -> Self::Output {
        self[0]
    }
}


impl G for u8 {
    fn g<B:F>(&self, b:B) ->B::Output {
        b.ff()
    }
}

fn f (x:u8) -> u8 {
    let xs = [x;5];
    x.g(xs)

}


const ARG: u8 = 23;


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
