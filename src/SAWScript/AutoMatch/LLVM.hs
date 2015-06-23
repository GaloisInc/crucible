{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.AutoMatch.LLVM where

import Control.Monad.State hiding (mapM)

import Text.LLVM hiding (parseDataLayout, Array, Double, Float, FloatType, Void)
import Verifier.LLVM.Codebase hiding ( Global, ppSymbol, ppIdent
                                     , globalSym, globalType )
--import qualified Verifier.LLVM.Codebase as CB
--import Verifier.LLVM.Codebase.LLVMContext
import Verifier.LLVM.Backend.SAW
--import Verifier.LLVM.Codebase.DataLayout
--import Verifier.LLVM.Codebase.AST
--import Verifier.LLVM.Simulator
--import Verifier.LLVM.Simulator.Internals

--import Verifier.SAW.FiniteValue
import Verifier.SAW.SharedTerm
--import Verifier.SAW.SCTypeCheck

--import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.Builtins
--import SAWScript.LLVMExpr
--import SAWScript.LLVMMethodSpecIR
--import SAWScript.LLVMMethodSpec
--import SAWScript.Options
--import SAWScript.Proof
--import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SV

import Data.Maybe

--import SAWScript.AutoMatch
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

getDeclsLLVM :: SharedContext SAWCtx -> LLVMModule -> {- LLVMSetup () -> -} IO (String,[Decl])
getDeclsLLVM sc (LLVMModule file mdl) {- _setup -} =

  let dataLayout = parseDataLayout $ modDataLayout mdl
      symbols = map defName (modDefines mdl)
  in do
    (sbe, _mem, _scLLVM) <- createSAWBackend' sawProxy dataLayout sc
    (warnings, cb) <- mkCodebase sbe dataLayout mdl
    forM_ warnings $ putStrLn . ("WARNING: " ++) . show
    return . (file,) . catMaybes . for symbols $ \symbol ->
      symDefineToDecl =<< lookupDefine symbol cb

   where

      symDefineToDecl symDefine =
         let Symbol name = sdName symDefine
             args = mapM (\(Ident an, at) -> Arg an <$> memTypeToStdType at) $ sdArgs symDefine
             retType = memTypeToStdType =<< sdRetType symDefine
         in Decl name <$> retType <*> args

      memTypeToStdType t = case t of
         IntType 8  -> Just $ bitSeqType 8
         IntType 16 -> Just $ bitSeqType 16
         IntType 32 -> Just $ bitSeqType 32
         IntType 64 -> Just $ bitSeqType 64
         FloatType  -> Nothing -- We don't support floating point types
         DoubleType -> Nothing -- We don't support floating point types
         PtrType (MemType _memType) -> Nothing
            --memTypeToStdType memType -- TODO: Support pointers
         ArrayType _size _memType -> Nothing -- TODO: Support arrays
         _ -> Nothing
