{-
Module       : UCCrux.LLVM.Newtypes.FunctionName
Description  : Newtype for names of functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Newtypes.FunctionName
  ( FunctionName
  , functionNameToString
  , functionNameFromString
  )
where

newtype FunctionName = FunctionName { functionNameToString :: String }
  deriving (Eq, Ord, Show)

-- | Inverse of 'functionNameToString'
functionNameFromString :: String -> FunctionName
functionNameFromString = FunctionName
