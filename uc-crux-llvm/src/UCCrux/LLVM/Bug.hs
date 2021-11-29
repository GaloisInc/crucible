{-
Module           : UCCrux.LLVM.Bug
Description      : Representation of possible bugs
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Bug
  ( Bug,
    bugBehavior,
    bugLoc,
    makeBug,
    ppBug,
    BugBehavior(..),
    ppBugBehavior,
    UndefinedBehaviorTag,
    getUndefinedBehaviorTag,
    makeUndefinedBehaviorTag,
  )
where

{- ORMOLU_DISABLE -}
import qualified Prettyprinter as PP

import qualified What4.ProgramLoc as What4

import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack, ppCallStack)
import           Lang.Crucible.LLVM.Errors (BadBehavior)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import           Lang.Crucible.LLVM.Errors.MemoryError (MemoryErrorReason)
import qualified Lang.Crucible.LLVM.Errors.MemoryError as MemErrors
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB

import           UCCrux.LLVM.Bug.UndefinedBehaviorTag (UndefinedBehaviorTag, getUndefinedBehaviorTag, makeUndefinedBehaviorTag)
import           UCCrux.LLVM.PP (ppProgramLoc)
{- ORMOLU_ENABLE -}

-- | This is different from 'Lang.Crucible.LLVM.Errors.BadBehavior' in that
-- it stores less data.
data BugBehavior
  = BBUndefinedBehaviorTag !UndefinedBehaviorTag
  | BBMemoryErrorReason !MemoryErrorReason
  deriving (Eq, Ord)

ppBugBehavior :: BugBehavior -> PP.Doc ann
ppBugBehavior =
  \case
    BBUndefinedBehaviorTag ub -> UB.explain (getUndefinedBehaviorTag ub)
    BBMemoryErrorReason mer -> MemErrors.ppMemoryErrorReason mer

instance PP.Pretty BugBehavior where
  pretty = ppBugBehavior

-- | A possible bug: What it is, and where it can occur.
data Bug =
  Bug
    { bugBehavior :: !BugBehavior
    , bugLoc :: !What4.ProgramLoc
    , bugCallStack :: !CallStack
    }
  deriving (Eq, Ord)

makeBug :: BadBehavior sym -> What4.ProgramLoc -> CallStack -> Bug
makeBug bb loc callStack =
  Bug
    { bugBehavior =
        case bb of
          LLVMErrors.BBUndefinedBehavior ub ->
            BBUndefinedBehaviorTag (makeUndefinedBehaviorTag ub)
          LLVMErrors.BBMemoryError (MemErrors.MemoryError _ rsn) ->
            BBMemoryErrorReason rsn,
      bugLoc = loc,
      bugCallStack = callStack
    }

ppBug :: Bug -> PP.Doc ann
ppBug (Bug bb loc callStack) =
  PP.vsep
    [ ppBugBehavior bb
    , PP.pretty "at" <> PP.pretty (ppProgramLoc loc)
    , PP.pretty "in context:"
    , PP.indent 2 (ppCallStack callStack)
    ]

-- | Non-lawful instance, only to be used in tests.
instance Show Bug where
  show = show . ppBug

instance PP.Pretty Bug where
  pretty = ppBug
