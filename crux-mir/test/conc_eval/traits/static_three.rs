enum Vec<A> { X(A) }

trait T {
  fn g<B>();
  fn h<B>() {}
}

impl<A> T for Vec<A> {
  fn g<B>() {}
  // Use default for `h`
}

fn f(_ : ()) -> u32 {
    // In crux-mir, this is `::T::g::<Vec<u8>, bool>()`
    <Vec<u8> as T>::g::<bool>();
    <Vec<u8> as T>::h::<bool>();
    2
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
