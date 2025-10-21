{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Debug
  ( LLVMCommand
  , llvmCommandExt
  , llvmExtImpl
  ) where

import Control.Lens qualified as Lens
import Data.Parameterized.Classes (knownRepr)
import Data.Parameterized.Some (Some(Some))
import Data.Text (Text)
import Data.Void (Void, absurd)
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.Debug (ExtImpl, CommandExt)
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.LLVM.MemModel qualified as Mem
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator.GlobalState qualified as C
import Prettyprinter as PP
import What4.Interface qualified as W4

data LLVMCommand
  = Memory
  deriving (Bounded, Enum)

instance PP.Pretty LLVMCommand where
  pretty = PP.pretty . name

abbrev :: LLVMCommand -> Text
abbrev =
  \case
    Memory -> "mem"

help :: LLVMCommand -> Text
help =
  \case
    Memory -> "Display LLVM memory"

name :: LLVMCommand -> Text
name =
  \case
    Memory -> "memory"

rMemory :: Debug.RegexRepr Debug.ArgTypeRepr Debug.Empty
rMemory = knownRepr

regex :: LLVMCommand -> Some (Debug.RegexRepr Debug.ArgTypeRepr)
regex =
  \case
    Memory -> Some rMemory

llvmCommandExt :: CommandExt LLVMCommand
llvmCommandExt =
  Debug.CommandExt
  { Debug.extAbbrev = abbrev
  , Debug.extDetail = const Nothing
  , Debug.extHelp = help
  , Debug.extList = [minBound..maxBound]
  , Debug.extName = name
  , Debug.extRegex = regex
  }

data LLVMResponse
  = RMemory (PP.Doc Void)
  | MissingRMemory

instance PP.Pretty LLVMResponse where
  pretty =
    \case
      RMemory mem -> fmap absurd mem
      MissingRMemory -> "LLVM memory global variable was undefined!"

type instance Debug.ResponseExt LLVMCommand = LLVMResponse

llvmExtImpl ::
  W4.IsExpr (W4.SymExpr sym) =>
  C.GlobalVar Mem.Mem ->
  ExtImpl LLVMCommand p sym ext t
llvmExtImpl mVar =
  Debug.ExtImpl $
    \case
      Memory ->
        Debug.CommandImpl
        { Debug.implRegex = rMemory
        , Debug.implBody =
            \ctx execState Debug.MEmpty -> do
              let result = Debug.EvalResult ctx C.ExecutionFeatureNoChange Debug.Ok
              case Debug.execStateSimState execState of
                Left notApplicable ->
                  pure result { Debug.evalResp = Debug.UserError (Debug.NotApplicable notApplicable) }
                Right (C.SomeSimState simState) -> do
                  let globs = simState Lens.^. C.stateTree . C.actFrame . C.gpGlobals
                  case C.lookupGlobal mVar globs of
                    Nothing -> pure result { Debug.evalResp = Debug.XResponse MissingRMemory }
                    Just mem ->
                      let resp = Debug.XResponse (RMemory (Mem.ppMem (Mem.memImplHeap mem))) in
                      pure result { Debug.evalResp = resp }
        }
