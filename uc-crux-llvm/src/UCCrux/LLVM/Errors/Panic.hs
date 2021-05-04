{-
Module       : UCCrux.LLVM.Errors.Panic
Description  : Dealing with unrecoverable errors
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}

module UCCrux.LLVM.Errors.Panic
  ( HasCallStack,
    CruxLLVMBugfinding,
    Panic,
    panic,
  )
where

{- ORMOLU_DISABLE -}
import Panic hiding (panic)
import qualified Panic
{- ORMOLU_ENABLE -}

data CruxLLVMBugfinding = CruxLLVMBugfinding

-- | `panic` represents an error condition that should only
--   arise due to a programming error. It will exit the program
--   and print a message asking users to open a ticket.
panic ::
  HasCallStack =>
  -- | Short name of where the error occured
  String ->
  -- | More detailed description of the error
  [String] ->
  a
panic = Panic.panic CruxLLVMBugfinding

instance PanicComponent CruxLLVMBugfinding where
  panicComponentName _ = "crux-llvm bugfinding mode"
  panicComponentIssues _ = "https://github.com/GaloisInc/crucible/issues"

  {-# NOINLINE panicComponentRevision #-}
  panicComponentRevision = $useGitRevision
