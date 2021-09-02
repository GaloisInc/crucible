{-
Module       : UCCrux.LLVM.Equivalence.Config
Description  : Configuration for crash-equivalence checking
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Equivalence.Config
  ( EquivalenceConfig(..)
  )
where

import UCCrux.LLVM.Config.FunctionName (FunctionName)

data EquivalenceConfig
  = EquivalenceConfig
      { equivModule :: FilePath,
        -- | Entry points. If empty, check functions that are in both modules.
        equivEntryPoints :: [FunctionName],
        equivStrict :: Bool
      }
  deriving (Eq, Ord, Show)
