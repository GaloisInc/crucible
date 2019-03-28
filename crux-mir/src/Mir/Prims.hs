{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

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

import Data.Semigroup

import Mir.DefId
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
loadPrims :: Bool -> Int -> IO Collection
loadPrims useStdLib debugLevel = do

  let lib = if useStdLib then
              [ "convert"
              , "option"
              , "result"
              , "cmp"      
              , "ops/range"  
              -- , "default"   -- doesn't include "implements" in mir-json
              , "ops/function"
              , "ops/index"
              , "ops/deref"
              , "slice"    -- need custom primitives (get_unchecked, compositional treatment of slices)
              ] else [
                "ops/function"  -- needed for any treatment of hofs
              ]
        
  
  -- Only print debugging info in the standard library at high debugging levels
  cols <- mapM (generateMIR (debugLevel-3) libLoc) lib
    
  let total = (fold (hardCoded : cols))
  when (debugLevel > 6) $ do
    Debug.traceM "--------------------------------------------------------------"
    Debug.traceM $ "Complete Collection: "
    Debug.traceM $ show (pretty total)
    Debug.traceM "--------------------------------------------------------------"  

  return total

hardCoded :: Collection
hardCoded = mempty

