
pub enum Res<T, E> {
        /// Contains the success value
        O(T),

        /// Contains the error value
        E(E),
    }


use Res::*;

impl <T, E> Res<T,E> {
    
    pub fn as_mut(&mut self) -> Res<&mut T, &mut E> {
        match *self {
           O(ref mut x) => O(x),
           E(ref mut x) => E(x),
        }
    }
}    


fn f (x : u32) -> () {
    let mut z : Res<u32,u32> = O(x);
    z.as_mut();
}

const ARG : u32 = 27;


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
