// FAIL: can't find dictionary

// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument 

struct Data<T>(T);

trait G<U> {
    fn g (&self) -> U;
}


impl G<u32> for u32 {
    fn g(&self) -> u32 {
        42
    }
}

impl<U> G<U> for Data<U> where U:G<U> {
    fn g(&self) -> U {
        (self.0).g()
    }
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    d.g()
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
