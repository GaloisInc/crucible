-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.VerificationHarness
-- Copyright        : (c) Galois, Inc 2017
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Support for manipulating compositional verification harnesses.
------------------------------------------------------------------------

module Lang.Crucible.Server.VerificationHarness where


import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.TypeCheck.AST as C

import qualified Lang.Crucible.Proto as P

type Offset = Integer

data HarnessVarType
  = HarnessVarWord Integer
    -- ^ A bitvector variable, with the given width.
    --   INVARIANT: the width is a multple of 8.
  | HarnessVarArray Integer Integer
    -- ^ A variable representing an array of bitvectors,
    --   with the given number of elements and word width.
    --   INVARIANT: the width is a multple of 8.

data HarnessVarDecl
  = HarnessVarDecl
  { harnessVarIdent :: C.Ident
  , harnessVarType  :: HarnessVarType
  }

data HarnessVar
  = CryptolVar C.Ident
    -- ^ A user-declared variable
  | ReturnAddressVar
    -- ^ The special built-in variable representing the
    --   return address
  | StackPositionVar
    -- ^ The special built-in variable representing the
    --   current stack pointer

data VerificationSetupStep
  = BindVariable HarnessVar C.Expr
  | RegisterVal Offset HarnessVar
  | MemPointsTo HarnessVar Offset HarnessVar

data VerificationPhase
  = VerificationPhase
  { phaseVars  :: [HarnessVarDecl]
  , phaseSetup :: [VerificationSetupStep]
  , phaseConds :: [C.Expr]
  }

data VerificationHarness
  = VerificationHarness
  { verificationOverrideName :: String
  , verificationPrestate     :: VerificationPhase
  , verificationPoststate    :: VerificationPhase
  }

processHarness ::
   P.VerificationHarness ->
   Either [String] VerificationHarness
processHarness _rawHarness =
   do Left ["FIXME implement process harness"]
