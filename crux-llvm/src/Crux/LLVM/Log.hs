{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module Crux.LLVM.Log
  ( CruxLLVMLogMessage (..),
    SupportsCruxLLVMLogMessage,
    cruxLLVMLogMessageToSayWhat,
    sayCruxLLVM,
  )
where

import Crux.Log (SayLevel (..), SayWhat (..), cruxLogTag)
import qualified Crux.Log as Log
import Data.Text as Text (Text, pack, unwords)

data CruxLLVMLogMessage
  = Breakpoint Text
  | ClangInvocation [Text]
  | Executable Text
  | FailedToBuildCounterexampleExecutable
  | SimulatingFunction Text
  | UsingPointerWidthForFile Integer Text

type SupportsCruxLLVMLogMessage msgs =
  (?injectCruxLLVMLogMessage :: CruxLLVMLogMessage -> msgs)

sayCruxLLVM ::
  Log.Logs msgs =>
  SupportsCruxLLVMLogMessage msgs =>
  CruxLLVMLogMessage ->
  IO ()
sayCruxLLVM msg =
  let ?injectMessage = ?injectCruxLLVMLogMessage
   in Log.say msg

clangLogTag :: Text
clangLogTag = "CLANG"

cruxLLVMLogMessageToSayWhat :: CruxLLVMLogMessage -> SayWhat
cruxLLVMLogMessageToSayWhat (ClangInvocation params) =
  SayWhat Noisily clangLogTag (Text.unwords params)
cruxLLVMLogMessageToSayWhat (Breakpoint line) =
  SayWhat Simply cruxLogTag ("*** break on line: " <> line)
cruxLLVMLogMessageToSayWhat (Executable exe) =
  SayWhat Simply cruxLogTag ("*** debug executable: " <> exe)
cruxLLVMLogMessageToSayWhat FailedToBuildCounterexampleExecutable =
  SayWhat Fail cruxLogTag "Failed to build counterexample executable"
cruxLLVMLogMessageToSayWhat (SimulatingFunction function) =
  SayWhat Simply cruxLogTag ("Simulating function " <> function)
cruxLLVMLogMessageToSayWhat (UsingPointerWidthForFile width file) =
  SayWhat
    Simply
    cruxLogTag
    ( Text.unwords
        [ "Using pointer width:",
          pack (show width),
          "for file",
          file
        ]
    )
