# next

## API changes

* Much of the `crux-mir` library has been split off into a `crucible-mir`
  library, which removes all of the `crux`-specific code. The following modules
  were _not_ migrated to `crucible-mir`:

  * `Mir.Generate`
  * `Mir.Language`
  * `Mir.Log`
  * `Mir.Concurrency`
  * `Mir.Overrides`

  Note that `Mir.Generate` now only exports the `generateMIR` function. The
  `parseMIR` and `translateMIR` functions have been moved to a new
  `Mir.ParseTranslate` module in `crucible-mir`.

# 0.6

## Bug fixes

* `Any`-typed local variables are no longer initialized to a default value,
  which prevents spurious assertion failures if these variables become involved
  in symbolic branches in certain cases.
