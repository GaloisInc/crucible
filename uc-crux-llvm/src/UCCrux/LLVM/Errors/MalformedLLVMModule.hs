{-
Module       : UCCrux.LLVM.Errors.MalformedLLVMModule
Description  : Problems with the (our assumptions about) the input program(s)
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Errors.MalformedLLVMModule
  ( malformedLLVMModule,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Void (Void)

import           Prettyprinter (Doc, pretty)

import qualified Lang.Crucible.LLVM.MalformedLLVMModule as M
{- ORMOLU_ENABLE -}

-- | Throw a 'Lang.Crucible.LLVM.MalformedLLVMModule.MalformedLLVMModule'
-- exception.
malformedLLVMModule ::
  -- | Function name
  String ->
  -- | Short explanation
  Doc Void ->
  -- | Details
  [Doc Void] ->
  a
malformedLLVMModule nm short details =
  M.malformedLLVMModule short $
    concat
      [ [ pretty ("In function: " ++ nm) ]
      , details
      , map
          pretty
          [ "This is either a bug in the compiler that produced the LLVM module",
            "or in UC-Crux's assumptions about the form of valid LLVM modules.",
            "Try running `opt -disable-output -verify < your-module.bc`.",
            "If opt reports no problems, please report this error here:",
            "https://github.com/GaloisInc/crucible/issues"
          ]
      ]
