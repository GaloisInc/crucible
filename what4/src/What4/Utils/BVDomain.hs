{-|
Module      : What4.Utils.BVDomain
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

Provides an implementation of bitvector abstract domains.
This module reexports either the "empty" implementation,
which does essentially no work, or the "maps" implementation.
This setup allows easy compile-time selection of an implementation,
for performance comparison purposes.
-}


module What4.Utils.BVDomain (module BVDomain) where


import What4.Utils.BVDomain.Map as BVDomain
