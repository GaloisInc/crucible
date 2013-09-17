{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.LLVMBuiltins where

import Control.Monad.Error
import Control.Monad.State

import qualified Text.LLVM as LLVM
import qualified Verifier.LLVM.Backend as L
import qualified Verifier.LLVM.Codebase as L
import qualified Verifier.LLVM.Backend.SAW as LSAW
import qualified Verifier.LLVM.Simulator as L

import Verifier.SAW.SharedTerm

import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value

import Verinf.Utils.LogMonad

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: SharedContext SAWCtx -> FilePath -> String -> LLVMSetup ()
            -> IO (SharedTerm SAWCtx)
extractLLVM sc file func _setup = do
  mdl <- L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
      sym = L.Symbol func
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- LSAW.createSAWBackend' be dl
    (_warnings, cb) <- L.mkCodebase sbe dl mdl
    -- TODO: Print warnings from codebase.
    case L.lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> L.runSimulator cb sbe mem Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (L.sdArgs md)
        _ <- L.callDefine sym (L.sdRetType md) args
        mrv <- L.getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just rv -> liftIO $ do
            lamTm <- bindExts scLLVM (map snd args) rv
            scImport sc lamTm


{-
extractLLVMBit :: FilePath -> String -> SC s (SharedTerm s')
extractLLVMBit file func = mkSC $ \_sc -> do
  mdl <- L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
      sym = L.Symbol func
      mg = L.defaultMemGeom dl
  withBE $ \be -> do
    LBit.SBEPair sbe mem <- return $ LBit.createBuddyAll be dl mg
    cb <- L.mkCodebase sbe dl mdl
    case L.lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> L.runSimulator cb sbe mem L.defaultSEH Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (L.sdArgs md)
        L.callDefine_ sym (L.sdRetType md) args
        mrv <- L.getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just bt -> fail "extractLLVMBit: not yet implemented"
-}

freshLLVMArg :: Monad m =>
            (t, L.MemType) -> L.Simulator sbe m (L.MemType, L.SBETerm sbe)
freshLLVMArg (_, ty@(L.IntType bw)) = do
  sbe <- gets L.symBE
  tm <- L.liftSBE $ L.freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."

verifyLLVM :: BuiltinContext -> Options -> String -> String
           -> [LLVMMethodSpecIR]
           -> LLVMSetup ()
           -> IO LLVMMethodSpecIR
verifyLLVM bic opts file func overrides setup = do
  let pos = fixPos -- TODO
      sc = biSharedContext bic
  mdl <- L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- LSAW.createSAWBackend' be dl
    (_warnings, cb) <- L.mkCodebase sbe dl mdl
    ms0 <- initLLVMMethodSpec pos cb func
    let lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsContext = scLLVM
                  }
    (_, lsctx) <- runStateT setup lsctx0
    let ms = lsSpec lsctx
    fail "verifyLLVM"
    return ms

llvmPure :: LLVMSetup ()
llvmPure = return ()

llvmVar :: BuiltinContext -> Options -> String -> Value SAWCtx
        -> LLVMSetup ()
llvmVar bic _ name t@(VCtorApp _ _) = do
  lsState <- get
  {-
  let ms = lsSpec lsState
      sym = undefined
  exp <- liftIO $ parseLLVMExpr (biLLVMCodebase bic) sym name
  let lty = lssTypeOfJavaExpr exp
      lty' = exportLSSType t
      aty = exportLLVMType t
  when (lty /= lty') $ fail $ show $
    hsep [ text "WARNING: Declared type"
         , text (show lty')
         , text "doesn't match actual type"
         , text (show lty)
         , text "for variable"
         , text name
         ]
  -}
  let (exp, aty) = undefined -- TODO
  modify $ \st -> st { lsSpec = specAddVarDecl name exp aty (lsSpec st) }
  -- TODO: Could return (llvm_value name) for convenience? (within SAWScript context)
llvmVar _ _ _ _ = fail "llvm_var called with invalid type argument"

llvmAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmAssert _ _ v =
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (AssertPred fixPos (mkLogicExpr v)) (lsSpec st) }

llvmAssertEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmAssertEq = fail "llvmAssertEq"

llvmEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmEnsureEq = fail "llvmEnsureEq"

llvmModify :: BuiltinContext -> Options -> String
           -> LLVMSetup ()
llvmModify = fail "llvmEnsureEq"

llvmReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmReturn _ _ t =
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand (Return (LogicE (mkLogicExpr t))) (lsSpec st) }

llvmVerifyTactic :: BuiltinContext -> Options -> ProofScript SAWCtx ProofResult
                 -> LLVMSetup ()
llvmVerifyTactic _ _ script =
  modify $ \st -> st { lsSpec = specSetVerifyTactic script (lsSpec st) }
