# 0.2 -- 2025-11-09

* Remove `resolveForwardDeclarationsHook`. Instead, use `bindFnHandle` in
  `setupHook`.
* Give `setupOverridesHook` the symbolic backend (`bak`) instead of the
  expression builder (`sym`). Use `Lang.Crucible.Backend.backendGetSym` to
  recover the latter from the former.

# 0.1 -- 2024-02-05

* Initial version. Split off from `crucible-syntax`.
