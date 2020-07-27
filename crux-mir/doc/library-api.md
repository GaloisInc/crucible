# Using `crux-mir` as a library

To load a MIR module and translate it to Crucible, call
`Mir.Generate.loadAndTranslateMIR`:

```Haskell
-- loadAndTranslateMIR :: FilePath -> HandleAllocator -> IO RustModule

halloc <- newHandleAllocator
rm <- loadAndTranslateMIR "path/to/module.json" halloc
```

The input file should be a JSON-formatted MIR module, as produced by `cargo
crux-test -- --print-mir-path` or by `crux-rustc --test`.  It is also legal to
provide a `.rs` source file, which `mir-verifier` will try to compile itself,
but this mode is mainly for testing purposes and is not very robust.  The
indexed/linkable `.mir` files produced by `mir-json` are not supported.

The output of translation is a `Mir.Generator.RustModule`, which contains
various useful pieces of information:

 * `rm ^. rmCFGs :: Map Text (AnyCFG MIR)`: A map containing the Crucible CFG
   for each translated function.  The keys are `DefId`s, whose format is
   described below.
 * `rm ^. rmCS :: Mir.Generator.CollectionState`: Contains various tables used
   during translation.  Might be useful for low-level interactions with the
   generated Crucible, like accessing the values of `static`s or manually
   constructing trait objects pointers.
 * `rm ^. rmCS.collection :: Mir.Mir.Collection`: The AST of the MIR module.
   The MIR code has already been linked at this point, so the `Collection`
   includes the code for both the main crate and all of its dependencies.
 * `rm ^. rmCS.collection.roots :: [DefId]`: Lists the entry points of the
   module, which are any functions marked `#[crux_test]` in the main crate.
 * `rm ^. rmCS.collection.intrinsics :: Map DefId Intrinsic`: Gives the origin
   of each function in the module, including its pre-monomorphization `DefId`
   and the type arguments (if any) used during monomorphization.  The name is
   somewhat misleading: these days, every function appears in the `intrinsics`
   table, not just compiler intrinsics.

## Finding a particular function

Finding the `DefId` of a particular Rust function can be somewhat difficult due
to the way names are mangled during the MIR export.

The easiest approach is to mark a single target function with `#[crux_test]`,
so that its `DefId` will be the sole entry in `rm ^. rmCS.collection.roots`.
Note that `#[crux_test]` only works in the main / top-level crate;
`#[crux_test]` functions inside the main crate's dependencies do not appear in
`roots`.  This also requires that the function is monomorphic, as
`#[crux_test]` doesn't work on functions that take type arguments.

The next-easiest way is to search `rm ^. rmCS.collection.intrinsics` for an
entry where `intrInst.inKind` is `IkItem` and `intrInst.inDefId.to idKey`
matches the `ExplodedDefId` of the target function.  `ExplodedDefId`s omit
crate and impl disambiguators, so they are easy to predict (though there is a
slight risk of name collisions if the build contains multiple versions of the
same crate or if the target function is an `impl` method).  For generic
functions, also check `intrInst.inSubsts` against the type arguments of the
desired monomorphization.

Note that only definitions required by some `#[crux_test]` function will appear
in the `Collection`.  Unused items will be discarded during MIR linking.  In
some cases, it may be necessary to define a `#[crux_test]` wrapper that calls
the function of interest.
