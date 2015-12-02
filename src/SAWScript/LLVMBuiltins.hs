{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Control.Monad.State hiding (mapM)
import Control.Monad.Trans.Except
import Data.List (partition)
import qualified Data.Map as Map
import Data.String
import qualified Data.Vector as V
import Text.Parsec as P

import Text.LLVM (modDataLayout)
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase hiding ( Global, ppSymbol, ppIdent
                                     , globalSym, globalType
                                     )
import qualified Verifier.LLVM.Codebase as CB
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals

import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer (asExtCns)
import Verifier.SAW.SharedTerm

import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.Builtins
import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec
import SAWScript.LLVMUtils
import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SV

import qualified Cryptol.TypeCheck.AST as Cryptol

type Backend = SAWBackend SAWCtx
type SAWTerm = SharedTerm SAWCtx
type SAWDefine = SymDefine SAWTerm

loadLLVMModule :: FilePath -> IO LLVMModule
loadLLVMModule file = LLVMModule file <$> loadModule file

-- LLVM memory operations

readLLVMTermAddr :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                    [SBETerm sbe] -> LLVMExpr
                 -> Simulator sbe m (SBETerm sbe)
readLLVMTermAddr args (Term e) =
  case e of
    Arg _ _ _ -> fail "Can't read address of argument"
    Global s _ -> evalExprInCC "readLLVMTerm:Global" (SValSymbol s)
    Deref ae _ -> readLLVMTerm args ae 1
    StructField ae si idx _ ->
      structFieldAddr si idx =<< readLLVMTerm args ae 1
    ReturnValue _ -> fail "Can't read address of return value"

writeLLVMTerm :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                 [SBETerm sbe]
              -> (LLVMExpr, SBETerm sbe, Integer)
              -> Simulator sbe m ()
writeLLVMTerm args (e, t, cnt) = do
  addr <- readLLVMTermAddr args e
  let ty = lssTypeOfLLVMExpr e
      ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
          | otherwise = ty
  dl <- getDL
  store ty' t addr (memTypeAlign dl ty')

readLLVMTerm :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                [SBETerm sbe]
             -> LLVMExpr
             -> Integer
             -> Simulator sbe m (SBETerm sbe)
readLLVMTerm args et@(Term e) cnt =
  case e of
    Arg n _ _ -> return (args !! n)
    ReturnValue _ -> do
      rslt <- getProgramReturnValue
      case rslt of
        (Just v) -> return v
        Nothing -> fail "Program did not return a value"
    _ -> do
      let ty = lssTypeOfLLVMExpr et
      addr <- readLLVMTermAddr args et
      let ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
              | otherwise = ty
      -- Type should be type of value, not type of ptr
      dl <- getDL
      load ty' addr (memTypeAlign dl ty')

-- LLVM verification and model extraction commands

type Assign = (LLVMExpr, TypedTerm SAWCtx)

missingSymMsg :: String -> Symbol -> String
missingSymMsg file (Symbol func) =
  "Bitcode file " ++ file ++ " does not contain symbol `" ++ func ++ "`."

startSimulator :: SharedContext s
               -> LSSOpts
               -> LLVMModule
               -> Symbol
               -> (SharedContext s
                   -> SBE (SAWBackend s)
                   -> Codebase (SAWBackend s)
                   -> DataLayout
                   -> SymDefine (SharedTerm s)
                   -> Simulator (SAWBackend s) IO a)
               -> IO a
startSimulator sc lopts (LLVMModule file mdl) sym body = do
  let dl = parseDataLayout $ modDataLayout mdl
  (sbe, mem, scLLVM) <- createSAWBackend' sawProxy dl sc
  (warnings, cb) <- mkCodebase sbe dl mdl
  forM_ warnings $ putStrLn . ("WARNING: " ++) . show
  case lookupDefine sym cb of
    Nothing -> fail $ missingSymMsg file sym
    Just md -> runSimulator cb sbe mem (Just lopts) $
               body scLLVM sbe cb dl md

symexecLLVM :: BuiltinContext
            -> Options
            -> LLVMModule
            -> String
            -> [(String, Integer)]
            -> [(String, SharedTerm SAWCtx, Integer)]
            -> [(String, Integer)]
            -> Bool
            -> IO (TypedTerm SAWCtx)
symexecLLVM bic opts lmod fname allocs inputs outputs doSat =
  let sym = Symbol fname
      sc = biSharedContext bic
      lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = doSat
                      }
  in startSimulator sc lopts lmod sym $ \scLLVM sbe cb dl md -> do
        setVerbosity (simVerbose opts)
        let verb = simVerbose opts
        let mkAssign (s, tm, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr cb md s
              return (e, tm, n)
            mkAllocAssign (s, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr cb md s
              case lssTypeOfLLVMExpr e of
                PtrType (MemType ty) -> do
                  tm <- allocSome n ty
                  when (verb >= 2) $ liftIO $ putStrLn $
                    "Allocated address: " ++ show tm
                  return (e, tm, 1)
                _ -> fail $ "Allocation parameter " ++ s ++
                            " does not have pointer type"
            allocSome n ty = do
              when (verb >= 2) $ liftIO $ putStrLn $
                "Allocating " ++ show n ++ " elements of type " ++ show (ppActualType ty)
              let aw = ptrBitwidth dl
              sz <- liftSBE (termInt sbe aw n)
              malloc ty aw sz
            mkOut (s, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr cb md s
              return (e, n)
            multDefErr i = error $ "Multiple terms given for " ++ ordinal (i + 1) ++
                                   " argument in function " ++ fname
            isArgAssign (e, _, _) = isArgLLVMExpr e
        allocAssigns <- mapM mkAllocAssign allocs
        assigns <- mapM mkAssign inputs
        let allAssigns = allocAssigns ++ assigns
            (argAssigns, otherAssigns) = partition isArgAssign allAssigns
            argMap =
              Map.fromListWithKey
              (\i _ _ -> multDefErr i)
              [ (idx, (tp, tm)) | (Term (Arg idx _ tp), tm, _) <- argAssigns ]
        let rargs = [(i, resolveType cb ty) | (i, ty) <- sdArgs md]
        args <- forM (zip [0..] rargs) $ \(i, (_, ty)) ->
                  case (Map.lookup i argMap, ty) of
                    (Just v, _) -> return v
                    -- (Nothing, PtrType (MemType dty)) -> (ty,) <$> allocSome 1 dty
                    _ -> fail $ "No binding for " ++ ordinal (i + 1) ++
                                " argument in function " ++ fname
        let argVals = map snd args
            retReg = (,Ident "__SAWScript_rslt") <$> sdRetType md
        _ <- callDefine' False sym retReg args
        -- TODO: the following line is generating memory errors
        mapM_ (writeLLVMTerm argVals) otherAssigns
        when (verb >= 2) $ liftIO $ putStrLn $ "Running " ++ fname
        run
        when (verb >= 2) $ liftIO $ putStrLn $ "Finished running " ++ fname
        outexprs <- mapM mkOut outputs
        outtms <- mapM (uncurry (readLLVMTerm argVals)) outexprs
        let bundle tms = case tms of
                           [t] -> return t
                           _ -> scTuple scLLVM tms
        liftIO (mkTypedTerm scLLVM =<< bundle outtms)


-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all arguments and
-- returns a lambda term representing the return value as a function of the
-- arguments. Many verifications will require more complex execution contexts.
extractLLVM :: BuiltinContext
            -> Options
            -> LLVMModule
            -> String
            -> LLVMSetup ()
            -> IO (TypedTerm SAWCtx)
extractLLVM bic opts lmod func _setup =
  let sym = Symbol func
      sc = biSharedContext bic
      lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = True
                      }
  in startSimulator sc lopts lmod sym $ \scLLVM _sbe _cb _dl md -> do
    setVerbosity (simVerbose opts)
    args <- mapM freshLLVMArg (sdArgs md)
    exts <- mapM (asExtCns . snd) args
    _ <- callDefine sym (sdRetType md) args
    mrv <- getProgramReturnValue
    case mrv of
      Nothing -> fail "No return value from simulated function."
      Just rv -> liftIO $ do
        lamTm <- bindExts scLLVM exts rv
        scImport sc lamTm >>= mkTypedTerm sc

freshLLVMArg :: Monad m =>
            (t, MemType) -> Simulator sbe m (MemType, SBETerm sbe)
freshLLVMArg (_, ty@(IntType bw)) = do
  sbe <- gets symBE
  tm <- liftSBE $ freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."


verifyLLVM :: BuiltinContext -> Options -> LLVMModule -> String
           -> [LLVMMethodSpecIR]
           -> LLVMSetup ()
           -> TopLevel LLVMMethodSpecIR
verifyLLVM bic opts (LLVMModule file mdl) funcname overrides setup =
  let pos = fixPos -- TODO
      dl = parseDataLayout $ modDataLayout mdl
      sc = biSharedContext bic
  in do
    (sbe, mem, scLLVM) <- io $ createSAWBackend' sawProxy dl sc
    (warnings, cb) <- io $ mkCodebase sbe dl mdl
    io $ forM_ warnings $ putStrLn . ("WARNING: " ++) . show
    func <- case lookupDefine (fromString funcname) cb of
      Nothing -> fail $ missingSymMsg file (Symbol funcname)
      Just def -> return def
    let ms0 = initLLVMMethodSpec pos cb func
        lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsTactic = Skip
                  , lsContext = scLLVM
                  , lsSimulate = True
                  , lsSatBranches = False
                  }
    (_, lsctx) <- runStateT setup lsctx0
    let ms = lsSpec lsctx
    let vp = VerifyParams { vpCode = cb
                          , vpContext = scLLVM
                          , vpOpts = opts
                          , vpSpec = ms
                          , vpOver = overrides
                          }
    let verb = verbLevel opts
    let overrideText =
          case overrides of
            [] -> ""
            irs -> " (overriding " ++ show (map specFunction irs) ++ ")"
    when (verb >= 2) $ io $ putStrLn $ "Starting verification of " ++ show (specName ms)
    let lopts = LSSOpts { optsErrorPathDetails = True
                        , optsSatAtBranches = lsSatBranches lsctx
                        }
    ro <- getTopLevelRO
    rw <- getTopLevelRW
    when (lsSimulate lsctx) $ io $ do
      when (verb >= 3) $ do
        putStrLn $ "Executing " ++ show (specName ms)
      runSimulator cb sbe mem (Just lopts) $ do
        setVerbosity verb
        esd <- initializeVerification scLLVM ms
        res <- mkSpecVC scLLVM vp esd
        when (verb >= 3) $ liftIO $ do
          putStrLn "Verifying the following:"
          mapM_ (print . ppPathVC) res
        case lsTactic lsctx of
          Skip -> liftIO $ putStrLn $
            "WARNING: skipping verification of " ++ show (specName ms)
          RunVerify script -> do
            let prv = prover opts scLLVM ms script
            liftIO $ fmap fst $ runTopLevel (runValidation prv vp scLLVM esd res) ro rw
    if lsSimulate lsctx
       then io $ putStrLn $ "Successfully verified " ++
                       show (specName ms) ++ overrideText
       else io $ putStrLn $ "WARNING: skipping simulation of " ++ show (specName ms)
    return ms

prover :: Options
       -> SharedContext SAWCtx
       -> LLVMMethodSpecIR
       -> ProofScript SAWCtx SV.SatResult
       -> VerifyState
       -> SharedTerm SAWCtx
       -> TopLevel ()
prover opts sc ms script vs g = do
  let exts = getAllExts g
      verb = verbLevel opts
  tt <- io (mkTypedTerm sc =<< bindExts sc exts g)
  r <- evalStateT script (ProofGoal Universal (vsVCName vs) tt)
  case r of
    SV.Unsat -> when (verb >= 3) $ io $ putStrLn "Valid."
    -- TODO: replace x with something in the following
    SV.Sat val -> io $ showCexResults sc ms vs exts [("x", val)]
    SV.SatMulti vals -> io $ showCexResults sc ms vs exts vals

showCexResults :: SharedContext SAWCtx
               -> LLVMMethodSpecIR
               -> VerifyState
               -> [ExtCns (SharedTerm SAWCtx)]
               -> [(String, FiniteValue)]
               -> IO ()
showCexResults sc ms vs exts vals = do
  putStrLn $ "When verifying " ++ show (specName ms) ++ ":"
  putStrLn $ "Proof of " ++ vsVCName vs ++ " failed."
  putStrLn $ "Counterexample: "
  mapM_ (\(n, v) -> putStrLn ("  " ++ n ++ ": " ++ show v)) vals
  if (length exts == length vals)
    then vsCounterexampleFn vs (cexEvalFn sc (zip exts (map snd vals))) >>= print
    else putStrLn "ERROR: Can't show result, wrong number of values"
  fail "Proof failed."

llvmPure :: LLVMSetup ()
llvmPure = return ()

type LLVMExprParser a = ParsecT String () IO a

failLeft :: (Monad m, Show s) => m (Either s a) -> m a
failLeft act = either (fail . show) return =<< act

checkProtoLLVMExpr :: (Monad m) =>
                      Codebase (SAWBackend SAWCtx)
                   -> SymDefine (SharedTerm SAWCtx)
                   -> ProtoLLVMExpr
                   -> ExceptT String m LLVMExpr
checkProtoLLVMExpr cb fn pe =
  case pe of
    PReturn ->
      case sdRetType fn of
        Just ty -> return (Term (ReturnValue ty))
        Nothing -> throwE "Function with void return type used with `return`."
    PVar x -> do
      let nid = fromString x
      case lookup nid numArgs of
        Just (n, ty) -> return (Term (Arg n nid ty))
        Nothing ->
          case lookupSym (Symbol x) cb of
            Just (Left gb) ->
              return (Term (Global (CB.globalSym gb) (CB.globalType gb)))
            _ -> throwE $ "Unknown variable: " ++ x
    PArg n | n < length numArgs -> do
               let (i, tp) = args !! n
               return (Term (Arg n i tp))
           | otherwise ->
               throwE $ "(Zero-based) argument index too large: " ++ show n
    PDeref de -> do
      e <- checkProtoLLVMExpr cb fn de
      case lssTypeOfLLVMExpr e of
        PtrType (MemType ty) -> return (Term (Deref e ty))
        ty -> throwE $
              "Attempting to apply * operation to non-pointer, of type " ++
              show (ppActualType ty)
    PField n se -> do
      e <- checkProtoLLVMExpr cb fn se
      case resolveType cb (lssTypeOfLLVMExpr e) of
        PtrType (MemType (StructType si))
          | n < siFieldCount si -> do
            let ty = fiType (siFields si V.! n)
            return (Term (StructField e si n ty))
          | otherwise -> throwE $ "Field out of range: " ++ show n
        ty ->
          throwE $ "Left side of -> is not a struct pointer: " ++
                   show (ppActualType ty)
  where
    args = [(i, resolveType cb ty) | (i, ty) <- sdArgs fn]
    numArgs = zipWith (\(i, ty) n -> (i, (n, ty))) args [(0::Int)..]

parseLLVMExpr :: (Monad m) =>
                 Codebase (SAWBackend SAWCtx)
              -> SymDefine (SharedTerm SAWCtx)
              -> String
              -> ExceptT String m LLVMExpr
parseLLVMExpr cb fn str =
  case parseProtoLLVMExpr str of
    Left err -> throwE ("Parse error: " ++ show err)
    Right e -> checkProtoLLVMExpr cb fn e

getLLVMExpr :: Monad m =>
               LLVMMethodSpecIR -> String
            -> m (LLVMExpr, MemType)
getLLVMExpr ms name = do
  case Map.lookup name (specLLVMExprNames ms) of
    -- TODO: maybe compute type differently?
    Just (_, expr) -> return (expr, lssTypeOfLLVMExpr expr)
    Nothing -> fail $ "LLVM name " ++ name ++ " has not been declared."

llvmInt :: Int -> SymType
llvmInt n = MemType (IntType n)

llvmFloat :: SymType
llvmFloat = MemType FloatType

llvmDouble :: SymType
llvmDouble = MemType DoubleType

llvmArray :: Int -> SymType -> SymType
llvmArray n (MemType t) = MemType (ArrayType n t)
llvmArray _ t =
  error $ "Unsupported array element type: " ++ show (ppSymType t)

llvmStruct :: String -> SymType
llvmStruct n = Alias (fromString n)

llvmNoSimulate :: LLVMSetup ()
llvmNoSimulate = modify (\s -> s { lsSimulate = False })

llvmSatBranches :: Bool -> LLVMSetup ()
llvmSatBranches doSat = modify (\s -> s { lsSatBranches = doSat })

llvmVar :: BuiltinContext -> Options -> String -> SymType
        -> LLVMSetup (TypedTerm SAWCtx)
llvmVar bic _ name sty = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
  lty <- case resolveSymType cb sty of
           MemType mty -> return mty
           rty -> fail $ "Unsupported type in llvm_var: " ++ show (ppSymType rty)
  funcDef <- case lookupDefine func cb of
               Just fd -> return fd
               Nothing -> fail $ "Function " ++ show func ++ " not found."
  expr <- failLeft $ runExceptT $ parseLLVMExpr cb funcDef name
  when (isPtrLLVMExpr expr) $ fail $
    "Used `llvm_var` for pointer expression `" ++ name ++
    "`. Use `llvm_ptr` instead."
  -- TODO: check compatibility before updating
  let expr' = updateLLVMExprType expr lty
  modify $ \st ->
    st { lsSpec = specAddVarDecl fixPos name expr' lty (lsSpec st) }
  let sc = biSharedContext bic
  mty <- liftIO $ logicTypeOfActual sc lty
  case mty of
    Just ty -> liftIO $ scLLVMValue sc ty name >>= mkTypedTerm sc
    Nothing -> fail $ "Unsupported type in llvm_var: " ++ show (ppMemType lty)

llvmPtr :: BuiltinContext -> Options -> String -> SymType
        -> LLVMSetup (TypedTerm SAWCtx)
llvmPtr bic _ name sty = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
      Just funcDef = lookupDefine func cb
  lty <- case resolveSymType cb sty of
           MemType mty -> return mty
           rty -> fail $ "Unsupported type in llvm_var: " ++ show (ppSymType rty)
  expr <- failLeft $ runExceptT $ parseLLVMExpr cb funcDef name
  unless (isPtrLLVMExpr expr) $ fail $
    "Used `llvm_ptr` for non-pointer expression `" ++ name ++
    "`. Use `llvm_var` instead."
  let pty = PtrType (MemType lty)
      -- TODO: check compatibility before updating
      expr' = updateLLVMExprType expr pty
      dexpr = Term (Deref expr' lty)
      dname = '*':name
  modify $ \st ->
    st { lsSpec = specAddVarDecl fixPos dname dexpr lty $
                  specAddVarDecl fixPos name expr' pty (lsSpec st) }
  let sc = biSharedContext bic
  mty <- liftIO $ logicTypeOfActual sc lty
  case mty of
    Just ty -> liftIO $ scLLVMValue sc ty dname >>= mkTypedTerm sc
    Nothing -> fail $ "Unsupported type in llvm_ptr: " ++ show (ppMemType lty)

llvmDeref :: BuiltinContext -> Options -> Value
          -> LLVMSetup (SharedTerm SAWCtx)
llvmDeref _bic _ _t = fail "llvm_deref not yet implemented"

checkCompatibleType :: String -> LLVMActualType -> Cryptol.Schema
                    -> LLVMSetup ()
checkCompatibleType msg aty schema = liftIO $ do
  case cryptolTypeOfActual aty of
    Nothing ->
      fail $ "Type is not translatable: " ++ show (ppMemType aty) ++
             " (" ++ msg ++ ")"
    Just lt -> do
      unless (Cryptol.Forall [] [] lt == schema) $ fail $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ show lt
                , "  Got: " ++ show schema
                , "  In context: " ++ msg
                ]

llvmAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmAssert bic _ v = do
  liftIO $ checkBoolean (biSharedContext bic) v
  let cmd = AssertPred fixPos (mkLogicExpr v)
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }

llvmAssertEq :: String -> TypedTerm SAWCtx -> LLVMSetup ()
llvmAssertEq name (TypedTerm schema t) = do
  ms <- gets lsSpec
  (expr, mty) <- getLLVMExpr ms name
  checkCompatibleType "llvm_assert_eq" mty schema
  modify $ \st ->
    st { lsSpec = specAddLogicAssignment fixPos expr (mkLogicExpr t) ms }

llvmEnsureEq :: String -> TypedTerm SAWCtx -> LLVMSetup ()
llvmEnsureEq name (TypedTerm schema t) = do
  ms <- gets lsSpec
  (expr, mty) <- getLLVMExpr ms name
  checkCompatibleType "llvm_ensure_eq" mty schema
  let cmd = Ensure fixPos expr (LogicE (mkLogicExpr t))
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }

llvmReturn :: TypedTerm SAWCtx -> LLVMSetup ()
llvmReturn (TypedTerm schema t) = do
  ms <- gets lsSpec
  case sdRetType (specDef ms) of
    Just mty -> do
      checkCompatibleType "llvm_return" mty schema
      let cmd = Return (LogicE (mkLogicExpr t))
      modify $ \st ->
        st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }
    Nothing -> fail "llvm_return called on void function"

llvmVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SV.SatResult
                 -> LLVMSetup ()
llvmVerifyTactic _ _ script =
  modify $ \st -> st { lsTactic = RunVerify script }
