{-
Module       : UCCrux.LLVM.Config.Seconds
Description  : Newtype for seconds
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module UCCrux.LLVM.Newtypes.Seconds
  ( Seconds
  , secondsToInt
  , secondsFromInt
  , secondsToMicroseconds
  )
where

newtype Seconds = Seconds { secondsToInt :: Int }
  deriving (Eq, Num, Ord, Show, Read)

-- | Inverse of 'secondsToInt'
secondsFromInt :: Int -> Seconds
secondsFromInt = Seconds

secondsToMicroseconds :: Seconds -> Int
secondsToMicroseconds = (* 1000000) . secondsToInt
