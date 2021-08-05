module Main where

import Crux.LLVM.Log (CruxLLVMLogMessage)
import Crux.Log (CruxLogMessage, SerializedLogProofObligation)
import CruxLLVMMain (CruxLLVMLogging)
import Data.Aeson.TypeScript.TH
  ( TypeScript (getTypeScriptDeclarations),
    formatTSDeclarations,
  )
import Data.Proxy (Proxy (Proxy))

main :: IO ()
main = do
  -- This plug-in generates declarations that don't quite fit our style.  It's
  -- easiest to just disable some ESLint warnings for it.
  putStrLn "/* eslint-disable @typescript-eslint/semi */"
  putStrLn "/* eslint-disable quotes */"
  putStrLn ""
  putStrLn
    ( formatTSDeclarations
        ( getTypeScriptDeclarations (Proxy :: Proxy CruxLLVMLogging)
            <> getTypeScriptDeclarations (Proxy :: Proxy CruxLogMessage)
            <> getTypeScriptDeclarations (Proxy :: Proxy CruxLLVMLogMessage)
            <> getTypeScriptDeclarations (Proxy :: Proxy SerializedLogProofObligation)
        )
    )
