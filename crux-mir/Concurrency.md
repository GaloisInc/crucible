# crux-mir concurrency

Crux-mir has experimental support for multithreaded programs. 

This document explains (1) how to use crux-mir to simualte multithreaded programs, (2)
what is currently supported, and (3) how to extend support for additional primitives.

## Setting up and running crux-mir with concurrency support

### Generating Rust libraries 

As explained in the [README.md](README.md), the Rust libraries must be
translated by `translate_libs.sh`.

Some library types, such as `std::sync::Arc`, use atomic primitives internally.
Naively exploring all thread interleavings due to executing these atomic load
and store instructions (currently) introduces a significiant performance
penalty, as the number of thread interleavings explodes. To avoid exploring
these interleavings (which should generally be unobservable), we can generate a
version of the libraries where these particular atomics are not modeled via:

    $ ./translate_libs.sh --no-model-internal-atomics

### Running crux-mir

Having generated the libraries, we can simply run `crux-mir` with concurrency support by
passing the flat `--concurrency`. For example, to run the tests in [mutex.rs](./test/concurrency/mutex/mutex.rs)
(via `cabal`):

    $ cabal v2-exec -- crux-mir --concurrency test/mutex/mutex.rs
    
## Modeled primitives

- Atomics (sequential consistency only)
- `std::sync::Mutex` `lock()` 
  - once drop code is supported, we can support unlock, but for now clients must
    call the `crucible_TEMP_unlock` method to release a lock.
- `std::thread::spawn` (but not via `Builder`)
- `std::thread::JoinHandle::join`

## Adding support 

Supporting a primitive requires reducing it to one of the primitives supported
by `Crucibles` (or, not unlikely, adding or modifying this set). 

Generally this works as follows: add a function to
[concurrency.rs](lib/libcore/crucible/concurrency.rs) that is designed to denote
one of the Crucibles primitives. Next, add a `Match` function to
`Mir.Concurrency` to recognize this function and return the appropriate
`Crucibles` primitive.

## Notes

### Resource Names

Ideally, it would be possible to assign names to dynamically allocated resources
such that, along a given control flow path, the same resource has the same name
across several executions. This is not generally the case, as the `Nonce`s used
to generate names persist across the exploration. Ideally, one would simply add
a new field to modeled types to store a nonce, invoke a special primitive, and
`crux-mir` would reset the nonce generator associated with this primitive on
each execution, e.g. something like:

in `libcore/sync/atomic.rs`:
```rust
pub struct AtomicBool {
    v: UnsafeCell<u8>,
    id: usize, //Nonce Value
}
...
impl AtomicBool {
  const fn new() {
    AtomicBool {
      //...
      id: crucible::concurrency::nonce(), //Not allowed in a const context
     //... 
     }
  }
}
```

in `libcore/crucible/concurrency.rs`:
```rust
pub fn nonce() -> usize {}
```

and finally ensure that the override for `nonce` uses a dedicated nonce
generator that can be reset on each execution.

As indicated above, this is not possible (so directly) when the constructor for
the type in question is `const`, as is the case with `atomic` values. It may
just be the case that the conversion from `Mir` to `Crucible` needs to add some
additional elaboration, e.g. after each `new` call, add a call to initialize the
`id` field.
