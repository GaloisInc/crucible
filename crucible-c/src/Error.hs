{-# Language ExistentialQuantification #-}
module Error (module Error, catch) where

import Control.Monad.IO.Class(MonadIO, liftIO)
import Control.Exception(Exception(..), SomeException(..), throwIO, catch)
import Data.Typeable(cast)

import Data.LLVM.BitCode (formatError)
import qualified Data.LLVM.BitCode as LLVM


import Lang.Crucible.Backend(ppAbortExecReason)
import Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..))

throwError :: MonadIO m => Error -> m a
throwError x = liftIO (throwIO x)


data Error =
    LLVMParseError LLVM.Error
  | BadFun
  | MissingFun String
  | Bug String
  | ClangError Int String String
  | EnvError String

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

    BadFun -> "Function should have no arguments"
    MissingFun nm -> "Cannot find code for " ++ show nm
    Bug x -> x
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]
    EnvError msg -> msg

ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec abt _gp -> show (ppAbortExecReason abt)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedBranch {}    -> "(Aborted branch?)"


