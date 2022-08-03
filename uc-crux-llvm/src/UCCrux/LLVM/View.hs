{-
Module           : UCCrux.LLVM.View
Description      : Less strongly-typed data structures for (de)serialization
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

Since many of the types in UC-Crux are type-parameterized GADTs, we can't
directly derive @FromJSON@ and @ToJSON@ instances for them. Indeed, we can't
even hand-write @FromJSON@ instances, as deserialization requires information
outside of what's in the JSON blob. Instead, we create non-GADT "views" of each
GADT, and derive @FromJSON@ and @ToJSON@ instances for those. Then, a further
"typechecking" phase converts from the views to the GADTs. This is slower than
hand-writing functions that directly (de)serialize the GADTs, but it has a
number of advantages:

* The "typechecking" code can be reused across serialized representations, e.g.,
  config files or command-line arguments.
* The untyped views may be reused in different contexts, e.g., deriving
  @Arbitrary@ instances from @Generic@ for property-based testing.
* The views may be used in larger data structures that can themselves derive
  @FromJSON@ and @ToJSON@.

The view datatypes are all in modules using the @StrictData@ language extension.
This is because their primary use is serialization, which will result in
complete evaluation, eliminating the benefits of laziness.

Note [JSON instance tweaks]: JSON instances for various datatypes are derived
using 'Data.Aeson.TH.deriveJSON', with some tweaks to
'Data.Aeson.defaultOptions'. These tweaks remove unnecessary Haskell idioms from
the JSON representation. For example, it's common in Haskell code for all record
selectors for the same type to share a common prefix, e.g., "pt" in

> data Point2D = Point2D { ptX :: Int, ptY :: Int }

This idiom is used in part to avoid name clashes due to the lack of namespacing
for record selectors. There is no need for the JSON representation to reflect
this implementation detail, and removing such prefixes makes the JSON more terse,
hopefully making it use less RAM/disk space and network bandwidth, and making
it easier to write by hand (especially for users not familiar with Haskell
coding conventions).
-}

module UCCrux.LLVM.View
  ( module UCCrux.LLVM.View.Constraint,
    module UCCrux.LLVM.View.Cursor,
    module UCCrux.LLVM.View.FullType,
    module UCCrux.LLVM.View.Precond,
    module UCCrux.LLVM.View.Postcond,
    module UCCrux.LLVM.View.Shape,
    module UCCrux.LLVM.View.Specs,
    module UCCrux.LLVM.View.Util,
  ) where

import UCCrux.LLVM.View.Constraint
import UCCrux.LLVM.View.Cursor
import UCCrux.LLVM.View.FullType
import UCCrux.LLVM.View.Postcond
import UCCrux.LLVM.View.Precond
import UCCrux.LLVM.View.Shape
import UCCrux.LLVM.View.Specs
import UCCrux.LLVM.View.Util
