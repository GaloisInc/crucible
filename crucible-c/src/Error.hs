{-# Language ExistentialQuantification, TypeApplications, ScopedTypeVariables, TypeFamilies #-}
{-# Language FlexibleContexts, ConstraintKinds #-}

module Error (module Error, catch) where

import Control.Monad.IO.Class(MonadIO)
import Control.Exception(catch)
import qualified Data.LLVM.BitCode as LLVM
import Lang.Crucible.Backend(ppAbortExecReason)
import Lang.Crucible.Simulator.ExecutionTree (AbortedResult(..))

import qualified Crux.Error    as Crux
import qualified Crux.Language as Crux

import Types(LangLLVM)

--
-- C-specific errors
--
data CError =
    ClangError Int String String
  | LLVMParseError LLVM.Error

ppCError :: CError -> String
ppCError err = case err of
    LLVMParseError e       -> LLVM.formatError e
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]

-- Currently unused
ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec abt _gp -> show (ppAbortExecReason abt)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedBranch {}    -> "(Aborted branch?)"

-- This is a really strange trick that lets us use throwCError in *before*
-- we have declared the instance of Crux.Language LangLLVM
type CERROR = (Crux.Language LangLLVM, Crux.LangError LangLLVM ~ CError)

throwCError :: (MonadIO m, CERROR) => CError -> m b
throwCError e = Crux.throwError @LangLLVM (Crux.Lang  e)
