{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lang.Crucible.Utils.Seconds
  ( Seconds
  , secondsToInt
  , secondsFromInt
  , secondsToMicroseconds
  ) where

newtype Seconds = Seconds { secondsToInt :: Int }
  deriving (Eq, Num, Ord, Show)

-- | Inverse of 'secondsToInt'
secondsFromInt :: Int -> Seconds
secondsFromInt = Seconds

secondsToMicroseconds :: Seconds -> Int
secondsToMicroseconds = (* 1000000) . secondsToInt
