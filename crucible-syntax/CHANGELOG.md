# next

* The type `ACFG` has been removed in favor of `Lang.Crucible.CFG.Reg.AnyCFG`,
  which serves a similar purpose (hiding the argument and return types). The
  CFG argument and return types can be recovered via
  `Lang.Crucible.CFG.Reg.{cfgArgTypes,cfgReturnType}`.
* `crucible-syntax` now supports simulating CFGs with language-specific syntax
  extensions:

  * `SimulateProgramHooks` now has a `setupHook` field that can run an arbitrary
    override action before simulation. (For example, this is used in
    `crucible-llvm-syntax` to initialize the LLVM memory global variable.)
  * `SimulateProgramHooks` now has an extra `ext` type variable so that hooks
    can be extension-specific.
* `execCommand` and related data types in `Lang.Crucible.Syntax.Prog` have been
  split off into a separate `crucible-cli` library.

# 0.3

* The return type of `prog`:

  ```hs
  TopParser s (Map GlobalName (Pair TypeRepr GlobalVar), [ACFG ext])
  ```

  Has been changed to:

  ```hs
  TopParser s (ParsedProgram ext)
  ```

  Where the `parsedProgGlobals :: Map GlobalName (Some GlobalVar)` and
  `parsedProgCFGs :: [ACFG ext]` fields of `ParsedProgram` now serve the roles
  previously filled by the first and second fields of the returned tuple. (Note
  that `Pair TypeRepr GlobalVar` has been simplified to `Some GlobalVar`, as
  the `TypeRepr` of a `GlobalVar` can be retrieved through its `globalType`
  field.)
* The type of `simulateProgram`'s last argument:

  ```hs
  simulateProgram
    :: ...
    -> (forall p sym ext t st fs. (IsSymInterface sym, sym ~ (ExprBuilder t st fs)) =>
          sym -> HandleAllocator -> IO [(FnBinding p sym ext,Position)])
    -> ...
  ```

  Has changed to the following:

  ```hs
  simulateProgram
    :: ...
    -> SimulateProgramHooks
    -> ...
  ```

  Where the `setupOverridesHook` field of `SimulateProgramHooks` now serves the
  role previously filled by the function argument.

* `crucible-syntax` now supports _forward declarations_. A forward declaration
  is like a function, but lacking a body, and is useful for situations where
  one does not know what the implementation of a function will be until after
  the `.cbl` file is parsed. See the `crucible-syntax` `README` for more
  information.

  There is also now an `extern` keyword, that acts like a forward declaration
  for global variables.

# 0.2

* Various functions now take a `?parserHooks :: ParserHooks ext` implicit
  argument, which supports arbitrary syntax extensions. Various data types now
  also have an additional `ext` type parameter, which represents the type of
  the parser extension being used. If you do not care about parser extensions,
  a reasonable default choice is `?parserHooks = defaultParserHooks`.
