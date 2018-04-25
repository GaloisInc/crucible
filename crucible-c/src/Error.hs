{-# Language ExistentialQuantification #-}
module Error (module Error, catch) where

import Control.Monad.IO.Class(MonadIO, liftIO)
import Control.Exception(Exception(..), SomeException(..), throwIO, catch)
import Data.Typeable(cast)

import Data.LLVM.BitCode (formatError)
import qualified Data.LLVM.BitCode as LLVM


import Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..))
import Lang.Crucible.Simulator.SimError
          (SimErrorReason(..),ppSimError,simErrorReasonMsg,simErrorReason)

import Lang.Crucible.LLVM.Extension(LLVM)

throwError :: MonadIO m => Error -> m a
throwError x = liftIO (throwIO x)

data Error =
    LLVMParseError LLVM.Error
  | FailedToProve (Maybe SimErrorReason)
                  (Maybe String) -- Counter example as C functions.
  | forall b arch.
      SimFail (AbortedResult b (LLVM arch))
  | BadFun
  | MissingFun String
  | Bug String

instance Show Error where
  show = show . ppError

instance Exception Error where
  toException      = SomeException
  fromException (SomeException e) = cast e
  displayException = ppError

ppError :: Error -> String
ppError err =
  case err of
    LLVMParseError e -> formatError e
    FailedToProve mb _ -> case mb of
                            Nothing -> "Assertion failed." -- shouldn't happen
                            Just s  -> simErrorReasonMsg s
    SimFail (AbortedExec e _)
      | AssertFailureSimError x <- simErrorReason e -> x
    SimFail x -> unlines ["Error during simulation:", ppErr x]
    BadFun -> "Function should have no arguments"
    MissingFun nm -> "Cannot find code for " ++ show nm
    Bug x -> x

ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec err _gp -> show (ppSimError err)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedInfeasible   -> "Assumptions too strong (dead code)"
    AbortedBranch {}    -> "(Aborted branch?)"


