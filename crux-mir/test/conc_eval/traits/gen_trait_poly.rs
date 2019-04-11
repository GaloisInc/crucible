// Invoke a dictionary method

struct Data<T>(T);

trait T {
    fn t<U> (&self, y:U) -> U;
}

impl T for u32 {
    fn t<U>(&self, y:U) -> U { y }
}
impl<S> T for Data<S> where S:T {
    fn t<U>(&self,y:U) -> U { self.0.t(y) }
}

fn h<U>(x:Data<U>) -> U where U : T, U:Copy {
    let y : U = x.0;
    x.t(y)
}


fn f(_: ()) -> u32 {
    let x : u32 = 12;
    let y = Data(x);
    h(y)
}


const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
