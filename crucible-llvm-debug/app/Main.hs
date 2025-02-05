{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Parameterized.NatRepr (knownNat)
import Data.Text.IO qualified as IO
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.Debug qualified as Debug
import Lang.Crucible.LLVM.MemModel qualified as Mem
import Lang.Crucible.LLVM.Syntax (emptyParserHooks, llvmParserHooks)

main :: IO ()
main = do
  halloc <- C.newHandleAllocator
  mVar <- Mem.mkMemVar "crucible-llvm-debug:mem" halloc
  let ?ptrWidth = knownNat @64
  let ?parserHooks = llvmParserHooks emptyParserHooks mVar
  let cmdExt = Debug.llvmCommandExt
  inputs <- Debug.defaultDebuggerInputs cmdExt
  Debug.bareDebuggerExt
    cmdExt
    (Debug.llvmExtImpl mVar)
    (let ?recordLLVMAnnotation = \_ _ _ -> pure () in
     llvmExtensionImpl Mem.defaultMemOptions)
    inputs
    Debug.defaultDebuggerOutputs
    IO.putStrLn
