{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.LLVMBuiltins where

import Control.Monad.Error hiding (mapM)
import Control.Monad.State hiding (mapM)
import Data.List (sort)
import Data.List.Split
import qualified Data.Map as Map
import Data.String
import Text.PrettyPrint.Leijen
import Text.Read (readMaybe)

import Text.LLVM (modDataLayout)
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase hiding (Global)
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Simulator

import Verifier.SAW.TypedAST (FlatTermF(..))
import Verifier.SAW.SharedTerm

import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.Builtins
import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value

import Verinf.Symbolic
import Verinf.Utils.LogMonad

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: SharedContext SAWCtx -> FilePath -> String -> LLVMSetup ()
            -> IO (SharedTerm SAWCtx)
extractLLVM sc file func _setup = do
  mdl <- loadModule file
  let dl = parseDataLayout $ modDataLayout mdl
      sym = Symbol func
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl
    (_warnings, cb) <- mkCodebase sbe dl mdl
    -- TODO: Print warnings from codebase.
    case lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> runSimulator cb sbe mem Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (sdArgs md)
        _ <- callDefine sym (sdRetType md) args
        mrv <- getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just rv -> liftIO $ do
            lamTm <- bindExts scLLVM (map snd args) rv
            scImport sc lamTm

{-
extractLLVMBit :: FilePath -> String -> SC s (SharedTerm s')
extractLLVMBit file func = mkSC $ \_sc -> do
  mdl <- loadModule file
  let dl = parseDataLayout $ modDataLayout mdl
      sym = Symbol func
      mg = defaultMemGeom dl
  withBE $ \be -> do
    LBit.SBEPair sbe mem <- return $ LBit.createBuddyAll be dl mg
    cb <- mkCodebase sbe dl mdl
    case lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> runSimulator cb sbe mem defaultSEH Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (sdArgs md)
        callDefine_ sym (sdRetType md) args
        mrv <- getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just bt -> fail "extractLLVMBit: not yet implemented"
-}

freshLLVMArg :: Monad m =>
            (t, MemType) -> Simulator sbe m (MemType, SBETerm sbe)
freshLLVMArg (_, ty@(IntType bw)) = do
  sbe <- gets symBE
  tm <- liftSBE $ freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."

verifyLLVM :: BuiltinContext -> Options -> String -> String
           -> [LLVMMethodSpecIR]
           -> LLVMSetup ()
           -> IO LLVMMethodSpecIR
verifyLLVM bic opts file func overrides setup = do
  let pos = fixPos -- TODO
      sc = biSharedContext bic
  mdl <- loadModule file
  let dl = parseDataLayout $ modDataLayout mdl
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl
    (_warnings, cb) <- mkCodebase sbe dl mdl
    let ms0 = initLLVMMethodSpec pos cb func
        lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsContext = scLLVM
                  }
    (_, lsctx) <- runStateT setup lsctx0
    let ms = lsSpec lsctx
    let vp = VerifyParams { vpCode = cb
                          , vpContext = scLLVM
                          , vpOpts = opts
                          , vpSpec = ms
                          , vpOver = overrides
                          }
    let verb = simVerbose (vpOpts vp)
    when (verb >= 2) $ putStrLn $ "Starting verification of " ++ show (specName ms)
    {-
    let configs = [ (bs, cl)
                  | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                  , cl <- bsRefEquivClasses bs
                  ] -}
    let lssOpts = Nothing -- FIXME
    do
    -- forM_ configs $ \(bs,cl) -> do
      when (verb >= 3) $ do
        putStrLn $ "Executing " ++ show (specName ms)
      runSimulator cb sbe mem lssOpts $ do
        esd <- initializeVerification scLLVM ms
        let isExtCns (STApp _ (FTermF (ExtCns e))) = True
            isExtCns _ = False
            initialExts =
              sort . filter isExtCns . map snd . esdInitialAssignments $ esd
        res <- mkSpecVC scLLVM vp esd
        liftIO $ mapM_ (print . ppPathVC) res
        when (verb >= 3) $ liftIO $ do
          putStrLn "Verifying the following:"
          mapM_ (print . ppPathVC) res
        let prover vs script g = do
              glam <- bindExts scLLVM initialExts g
              glam' <- scImport (biSharedContext bic) glam
              Theorem thm <- provePrim (biSharedContext bic) script glam'
              when (verb >= 3) $ putStrLn $ "Proved: " ++ show thm
        liftIO $ runValidation prover vp scLLVM esd res
    return ms

llvmPure :: LLVMSetup ()
llvmPure = return ()

parseLLVMExpr :: Codebase (SAWBackend LSSCtx Lit)
              -> SymDefine (SharedTerm LSSCtx)
              -> String
              -> IO LLVMExpr
parseLLVMExpr cb fn = parseParts . reverse . splitOn "."
  where parseParts [] = fail "empty LLVM expression"
        parseParts [s] =
          case s of
            ('*':rest) -> do
              e <- parseParts [rest]
              undefined
            ('a':'r':'g':'s':'[':rest) -> do
              let num = fst (break (==']') rest)
              case readMaybe num of
                Just (n :: Int) -> undefined
                Nothing -> fail $ "bad LLVM expression syntax: " ++ s
            _ -> do
              let numArgs = zipWith (\(i, ty) n -> (i, (n, ty)))
                                    (sdArgs fn)
                                    [0..]
                  nid = fromString s
              case lookup nid numArgs of
                Just (n, ty) -> return (Term (Arg n nid ty))
                Nothing ->
                  case lookupSym (Symbol s) cb of
                    Just (Left gb) ->
                      return (Term (Global (globalSym gb) (globalType gb)))
                    _ -> fail $ "Can't parse variable name: " ++ s
        parseParts (f:rest) = do
          e <- parseParts rest
          let lt = lssTypeOfLLVMExpr e
              pos = fixPos -- TODO
          undefined

getLLVMExpr :: Monad m =>
               LLVMMethodSpecIR -> String
            -> m (LLVMExpr, MemType)
getLLVMExpr ms name = do
  case Map.lookup name (specLLVMExprNames ms) of
    Just exp -> return (exp, lssTypeOfLLVMExpr exp)
    Nothing -> fail $ "LLVM name " ++ name ++ " has not been declared."

exportLLVMType :: Value s -> MemType
exportLLVMType (VCtorApp "LLVM.IntType" [VInteger n]) =
  IntType (fromIntegral n)
exportLLVMType (VCtorApp "LLVM.ArrayType" [VInteger n, ety]) =
  ArrayType (fromIntegral n) (exportLLVMType ety)
exportLLVMType v =
  error $ "exportLLVMType: Can't translate to LLVM type: " ++ show v

llvmVar :: BuiltinContext -> Options -> String -> Value SAWCtx
        -> LLVMSetup (SharedTerm SAWCtx)
llvmVar bic _ name t = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
      Just funcDef = lookupDefine func cb
  exp <- liftIO $ parseLLVMExpr cb funcDef name
  let lty = lssTypeOfLLVMExpr exp
      lty' = exportLLVMType t
  when (lty /= lty') $ fail $ show $
    hsep [ text "WARNING: Declared type"
         , ppActualType lty'
         , text "doesn't match actual type"
         , ppActualType lty
         , text "for variable"
         , text name
         ]
  modify $ \st -> st { lsSpec = specAddVarDecl fixPos name exp lty (lsSpec st) }
  let sc = biSharedContext bic
  Just ty <- liftIO $ logicTypeOfActual sc lty
  liftIO $ scLLVMValue sc ty name

{-
llvmMayAlias :: BuiltinContext -> Options -> [String]
             -> LLVMSetup ()
llvmMayAlias bic _ exprs = do
  lsState <- get
  let ms = lsSpec lsState
      cb = specCodebase ms
      func = specFunction ms
  exprs <- liftIO $ mapM (parseLLVMExpr cb func) exprs
  modify $ \st -> st { lsSpec = specAddAliasSet exprs (lsSpec st) }
-}

llvmAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmAssert _ _ v =
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (AssertPred fixPos (mkLogicExpr v)) (lsSpec st) }

llvmAssertEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> LLVMSetup ()
llvmAssertEq bic _ name t = do
  ms <- gets lsSpec
  (exp, ty) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec = specAddLogicAssignment fixPos exp (mkLogicExpr t) ms }

llvmEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmEnsureEq = fail "llvmEnsureEq"

llvmModify :: BuiltinContext -> Options -> String
           -> LLVMSetup ()
llvmModify = fail "llvmModify"

llvmReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmReturn _ _ t =
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand (Return (LogicE (mkLogicExpr t))) (lsSpec st) }

llvmVerifyTactic :: BuiltinContext -> Options -> ProofScript SAWCtx ProofResult
                 -> LLVMSetup ()
llvmVerifyTactic _ _ script =
  modify $ \st -> st { lsSpec = specSetVerifyTactic script (lsSpec st) }
