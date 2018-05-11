{-# Language ExistentialQuantification #-}
module Error (module Error, catch) where

import Control.Monad.IO.Class(MonadIO, liftIO)
import Control.Exception(Exception(..), SomeException(..), throwIO, catch)
import Control.Lens((^.))
import Data.Typeable(cast)
import qualified Data.Text as Text

import Data.LLVM.BitCode (formatError)
import qualified Data.LLVM.BitCode as LLVM


import What4.ProgramLoc(plSourceLoc,Position(..))

import Lang.Crucible.Simulator.ExecutionTree
          (AbortedResult(..), SomeFrame(..), gpValue, ppExceptionContext)
import Lang.Crucible.Simulator.SimError
          (SimError(..), SimErrorReason(..),ppSimError
          ,simErrorReasonMsg )
import Lang.Crucible.Simulator.Frame(SimFrame)

import Lang.Crucible.LLVM.Extension(LLVM)

throwError :: MonadIO m => Error -> m a
throwError x = liftIO (throwIO x)


data Error =
    LLVMParseError LLVM.Error
  | FailedToProve SimError
                  (Maybe String) -- Counter example as C functions.
  | forall sym arch. SimFail SimError [ SomeFrame (SimFrame sym (LLVM arch)) ]
  | forall sym arch. SimAbort (AbortedResult sym (LLVM arch))
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
    FailedToProve e _ -> docLoc ++ txt
      where
      docLoc =
        case plSourceLoc (simErrorLoc e) of
          SourcePos f l c ->
            Text.unpack f ++ ":" ++ show l ++ ":" ++ show c ++ " "
          _ -> ""
      txt = simErrorReasonMsg (simErrorReason e)

    SimFail e fs -> ppE e fs
    SimAbort ab ->
      case ab of
        AbortedExec e p -> ppE e [ SomeFrame (p ^. gpValue) ]
        AbortedExit c ->
          unlines [ "Program terminated with exit code: " ++ show c ]
        AbortedBranch {} -> "XXX: Aborted branch?"

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

  where
  ppE e fs = unlines $ ("*** " ++ show (ppSimError e))
                     : [ "*** " ++ l | l <- lines (show (ppExceptionContext fs)) ]

ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec (SimError _ InfeasibleBranchError) _gp -> "Assumptions too strong (dead code)"
    AbortedExec err _gp -> show (ppSimError err)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedBranch {}    -> "(Aborted branch?)"


