{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.SAWCorePrimitives
( concretePrimitives
, bitblastPrimitives
, sbvPrimitives
) where

import qualified Data.Map as M
import Data.Map ( Map )

import qualified Data.AIG as AIG

import Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.Simulator.SBV as SBVSim
import qualified Verifier.SAW.Simulator.Concrete as Concrete

import qualified Verifier.SAW.Cryptol.Prims as CryPrims

concretePrimitives :: Map Ident Concrete.CValue
concretePrimitives = M.unions
  [ CryPrims.concretePrims
  ]

bitblastPrimitives :: AIG.IsAIG l g => g s -> Map Ident (BBSim.BValue (l s))
bitblastPrimitives g = M.unions
  [ CryPrims.bitblastPrims g
  ]

sbvPrimitives :: Map Ident SBVSim.SValue
sbvPrimitives = M.unions
  [ CryPrims.sbvPrims
  ]
