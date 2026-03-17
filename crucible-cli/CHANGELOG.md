# next

* Test-specific overrides (`proveObligations` and `crucible-print-assumption-state`)
  have been moved from `crucible-syntax`'s `Lang.Crucible.Syntax.Overrides` module
  into the `crucible-cli` test suite's `Overrides` module. This prevents library
  consumers from having to compile test-specific code. The main CLI applications
  no longer register these overrides by default.

# 0.2 -- 2025-11-09

* Remove `resolveForwardDeclarationsHook`. Instead, use `bindFnHandle` in
  `setupHook`.
* Give `setupOverridesHook` the symbolic backend (`bak`) instead of the
  expression builder (`sym`). Use `Lang.Crucible.Backend.backendGetSym` to
  recover the latter from the former.

# 0.1 -- 2024-02-05

* Initial version. Split off from `crucible-syntax`.
