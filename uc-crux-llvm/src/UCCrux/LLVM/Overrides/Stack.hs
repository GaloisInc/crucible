{-
Module       : UCCrux.LLVM.Overrides.Stack
Description  : Crucible call stack
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Overrides.Stack
  ( Stack,
    ppStack,
    collectStack
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (to, use)

import qualified Prettyprinter as PP

import qualified Lang.Crucible.Simulator.CallFrame as Crucible (SimFrame)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import           Lang.Crucible.Simulator.OverrideSim (OverrideSim)

import           Lang.Crucible.LLVM.Intrinsics (LLVM)
{- ORMOLU_ENABLE -}

newtype Stack' sym ext =
  Stack { getStack :: [Crucible.SomeFrame (Crucible.SimFrame sym ext)] }

type Stack sym = Stack' sym LLVM

ppStack :: Stack' sym ext -> PP.Doc ann
ppStack = Crucible.ppExceptionContext . getStack

collectStack :: OverrideSim p sym ext rtp args ret (Stack' sym ext)
collectStack = Stack <$> use (Crucible.stateTree . to Crucible.activeFrames)
