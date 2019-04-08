trait A {
    fn a(&self) -> u32;
}
trait B : A {
    fn b(&self) -> u32;
}


impl A for u32 {
    fn a(&self) -> u32 { *self }
}
impl B for u32 {
    fn b(&self) -> u32 { *self + self.a() }
}

fn g<T>(x : T) -> u32 where T : B {
    x.b()
}

fn f(_: ()) -> u32 {
    let d : u32 = 32;
    g (d)
}


const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
