#![cfg_attr(not(with_main), no_std)]
trait FIndex<A> {

    type Output : ?Sized;

    fn findex<B>(&self, i:usize, j:A, k:B) -> &Self::Output;

}

impl FIndex<i8> for [u8] {
    type Output = u8;
    fn findex<B>(&self, i:usize, _j:i8,_k:B) -> &Self::Output {
        &self[i]
    }
}


fn g<A,B> (x:&A, y:B) -> &<A as FIndex<B>>::Output where A : FIndex<B> {
    let z : i8 = 2;
    x.findex(0,y,z)
}

fn h<A> (x:&A) -> &<A as FIndex<i32>>::Output where A : FIndex<i32> {
    let z : i8 = 2;
    x.findex(0,3,z)
}


fn f (x:u8) -> u8 {
    let xs = [x;5];
    *xs.findex(0,1,x)
}


const ARG: u8 = 23;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u8 { f(ARG) }
