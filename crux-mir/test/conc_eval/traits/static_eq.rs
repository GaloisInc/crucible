struct Data(u32);

trait Eq {
    fn eq (&self, other : &Self) -> bool;
}

impl Eq for Data {
    fn eq (&self, other: &Data) -> bool {
        self.0 == other.0
    }
}

fn f(_: ()) -> bool {
    let d = Data(32);
    d.eq(&d)
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
