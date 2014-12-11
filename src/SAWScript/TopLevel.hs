{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SAWScript.TopLevel (
    -- * TopLevel Monad
    TopLevel(..), runTopLevel
  , io
  ) where

import Control.Applicative (Applicative)

newtype TopLevel a = TopLevel (IO a)
  deriving (Functor, Applicative, Monad)

runTopLevel :: TopLevel a -> IO a
runTopLevel (TopLevel m) = m

io :: IO a -> TopLevel a
io action = TopLevel action
