// FAIL: Don't know how to call ::G::g
//
// a static trait invocation for a polymorphic type
// calling the g method in h requires a dictionary argument 

struct Data(u32);

trait G {
    fn g (&self) -> u32;
}

impl G for Data {
    fn g(&self) -> u32 {
        self.0
    }
}

fn h<T>(x:T) -> u32 where T:G {
    x.g()
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    h(d)
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
