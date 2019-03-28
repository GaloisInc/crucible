// FAIL: cannot handle generic trait impls
// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument 

struct Data<T>(T);

trait G {
    fn g (&self) -> u32;
}

impl G for u32 {
    fn g(&self) -> u32 {
        return 1
    }
}

impl <T:G> G for Data<T> {
    fn g(&self) -> u32 {
       self.0.g()
    }
}


fn h<T>(x:T) -> u32 where T:G {
    x.g()
}

fn f(_: ()) -> u32 {
    let d = Data(Data(32));
    d.g()
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
