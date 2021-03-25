Adds support for WebAssembly (WASM) analysis to crucible.

Support is currently very preliminary; more work is probably needed
for full WASM capabilities.

## Use of haskell-wasm

Note that the `crucible-wasm` library uses the `haskell-wasm` package
as a dependency.  There are a couple of oddities currently in
existence for the `haskell-wasm` package:

 1. The hackage upload of `haskell-wasm` is version 1.0.0, but the
    _newer_ repository sources have an older package version.

    If your compilation is failing when building `haskell-wasm` then
    it's likely that it's using the 1.0.0 version from hackage because
    the constraint solver thinks that's the more recent version.
    There's a GaloisInc fork that updates the git to have a version of
    1.0.1.0 to avoid this issue, but see item #2 below.

 2. The `haskell-wasm` package uses a `package.yaml` that is intended
    to be processed by `hpack` to generate a `.cabal` file.  When
    checking out `crucible` and working on the `crucible-wasm` module,
    the `hpack` utility must be run after checking out the submodules
    and before running a cabal operation because otherwise there is no
    `.cabal` file for the `cabal.project` to find and it will fallback
    to using the hackage version.

    ```shell
    $ git clone crucible
    $ cd crucible
    $ git submodule update --init
    $ (cd dependencies/haskell-wasm; hpack)
    $ cabal build
    ```
