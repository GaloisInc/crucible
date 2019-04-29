{-# Language ExistentialQuantification #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ScopedTypeVariables #-}

module Crux.Error (module Crux.Error, catch) where

import Control.Monad.IO.Class(MonadIO, liftIO)
import Control.Exception(Exception(..), SomeException(..), throwIO, catch)
import Data.Typeable(cast)

import Lang.Crucible.Backend(ppAbortExecReason)
import Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..))

import Crux.Language
import Control.Exception

throwError :: forall a m b. (MonadIO m, Language a) => Error a -> m b
throwError x = liftIO (throwIO x)

data Error a =
    BadFun
  | MissingFun String
  | Bug String
  | EnvError String
  | Lang (LangError a)

instance Language a => Show (Error a) where
  show = ppError

instance Language a => Exception (Error a) where
  toException      = SomeException
  fromException (SomeException e) = cast e
  displayException = ppError

ppError :: forall a. (Language a) => Error a -> String
ppError err =
  case err of
    Lang x -> formatError @a x

    BadFun -> "Function should have no arguments"
    MissingFun nm -> "Cannot find code for " ++ show nm
    Bug x -> x
    EnvError msg -> msg


ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec abt _gp -> show (ppAbortExecReason abt)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedBranch {}    -> "(Aborted branch?)"

-- Throwing basic Crux Exceptions, without the Language
throwBadFun :: a
throwBadFun = throw (BadFun @Trivial)

throwMissingFun :: String -> a
throwMissingFun s = throw (MissingFun @Trivial s)

throwBug :: String -> a
throwBug s = throw (Bug @Trivial s)

throwEnvError :: String -> a
throwEnvError s = throw (EnvError @Trivial s)
