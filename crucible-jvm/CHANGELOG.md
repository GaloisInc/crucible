# next

* Add support for GHC 9.12 (at 9.12.2) and bump from 9.10.1 to 9.10.3.
* Fix a bug in which Java's floating-point `%` operator would incorrectly round
  an intermediate result to the nearest even number instead of rounding towards
  zero. (For instance, `5.0 % 3.0` would incorrectly evaluate to `-1.0` instead
  of `2.0`.)

# 0.2.1 -- 2025-11-09

* Store debugger state in the Crucible personality.

# 0.2 -- 2024-02-05

* Change `jvmOverride_def` in `Lang.Crucible.JVM.Overrides` to use a
  `TypedOverride`.
