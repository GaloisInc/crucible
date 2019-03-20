// FAIL: mir-json encoding of constant array
mod constants {
    pub(crate) const L: [u64;1] = [ 1 ];
}



const ARG: u64 = 20;

fn f(_w : u64 ) -> u64 {
    constants::L[0] 
}


#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
