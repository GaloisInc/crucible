// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(i128_type)]
#![crate_type = "lib"]
#![no_implicit_prelude]

pub mod ops {
    mod function {
        
        pub trait Fn<Args> : FnMut<Args> {
            fn call(&self, args: Args) -> Self::Output;
        } 

        pub trait FnMut<Args> : FnOnce<Args> {
            fn call_mut(&mut self, args: Args) -> Self::Output;
        } 
        pub trait FnOnce<Args> {
            type Output;
            
            fn call_once(self, args: Args) -> Self::Output;
        }

        /*
        mod impls {

            use ops::function::Fn;
            use ops::function::FnMut;
            use ops::function::FnOnce;
            use std::marker::Sized;

            impl<'a, A,F:?Sized> Fn<A> for &'a F
            where F : Fn<A>
            {
                fn call(&self, args: A) -> F::Output {
                    (**self).call(args)
                }
            }

            impl<'a, A,F:?Sized> FnMut<A> for &'a F
            where F : Fn<A>
            {
                fn call_mut(&mut self, args: A) -> F::Output {
                    (**self).call(args)
                }
            }

            impl<'a, A,F:?Sized> FnOnce<A> for &'a F
            where F : Fn<A>
            {
                type Output = F::Output;
                
                fn call_once(self, args: A) -> F::Output {
                    (*self).call(args)
                }
            }

            impl<'a, A,F:?Sized> FnMut<A> for &'a mut F
            where F : FnMut<A>
            {
                fn call_mut(&mut self, args: A) -> F::Output {
                    (*self).call_mut(args)
                }
            }
            
            impl<'a, A,F:?Sized> FnOnce<A> for &'a mut F
            where F : FnMut<A>
            {
                type Output = F::Output;
                fn call_once(self, args: A) -> F::Output {
                    (*self).call_mut(args)
                }
            }

        } */
    }
}
