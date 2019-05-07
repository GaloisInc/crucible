{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}

{-# OPTIONS_GHC -Wall -fwarn-incomplete-patterns #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Prims
-- Description      : Define the standard library
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Stability        : provisional
--
-- This module creates a collection of standard library traits, functions
-- and ADT definitions. Most of this library is defined by the "mir-lib"
-- package.
-----------------------------------------------------------------------

module Mir.Prims where

import Mir.Mir
import Mir.Generate
import Mir.PP()
import Data.Foldable(fold)

import Text.PrettyPrint.ANSI.Leijen (pretty)
import qualified Debug.Trace as Debug
import Control.Monad(when)


-- | Location of the rust file with the standard library
libLoc :: String
libLoc = "mir-lib/src/"

-- | load the rs file containing the standard library
loadPrims :: (?debug::Int) => Bool -> IO Collection
loadPrims useStdLib = do

  
  -- Same order as in https://github.com/rust-lang/rust/blob/master/src/libcore/prelude/v1.rs  
  let lib = if useStdLib then
              [ "ops/function"
              , "ops/try"
              , "clone"
              , "cmp"                    
--              , "convert"
              , "default"   -- NOTE: macro impls not available b/c mir-json doesn't include "implements"
              , "option"
              , "result"
              , "ops/range"  
              , "ops/index"
              , "ops/deref"
--              , "iter/traits/collect"  -- Cannot handle IntoIterator or FromIterator
--              , "iter/iterator"
              , "slice"    -- need custom primitives (get_unchecked, compositional treatment of slices)
--              , "ops/arith" -- doesn't include "implements" in mir-json for macros
              ] else [
                "ops/function"  -- needed for any treatment of hofs
              ]
        
  
  -- Only print debugging info in the standard library at high debugging levels
  
  cols <- let ?debug = ?debug - 3 in
          mapM (generateMIR libLoc) lib
    
  let total = (fold (hardCoded : cols))
  when (?debug > 6) $ do
    Debug.traceM "--------------------------------------------------------------"
    Debug.traceM $ "Complete Collection: "
    Debug.traceM $ show (pretty total)
    Debug.traceM "--------------------------------------------------------------"  

  return total

hardCoded :: Collection
hardCoded = mempty

