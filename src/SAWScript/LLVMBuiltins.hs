{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
module SAWScript.LLVMBuiltins where

import Control.Applicative hiding (many)
import Control.Monad.State hiding (mapM)
import Data.List (partition)
import qualified Data.Map as Map
import Data.Maybe
import Data.String
import qualified Data.Vector as V
import Text.Parsec as P
import Text.PrettyPrint.HughesPJ as PP
import Text.Read (readMaybe)

import Text.LLVM ( modTypes, modGlobals, modDeclares, modDefines, modDataLayout
                 , defName, defRetType, defVarArgs, defArgs, defAttrs
                 , funLinkage, funGC
                 , globalAttrs, globalSym, globalType
                 , ppType, ppGC, ppArgList,  ppLinkage, ppTyped,  ppTypeDecl
                 , ppDeclare, ppGlobalAttrs, ppMaybe, ppSymbol, ppIdent
                 )
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase hiding ( Global, ppSymbol, ppIdent
                                     , globalSym, globalType
                                     )
import qualified Verifier.LLVM.Codebase as CB
import Verifier.LLVM.Codebase.LLVMContext
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals

import Verifier.SAW.FiniteValue
import Verifier.SAW.SharedTerm

import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.Builtins
import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec
import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SV

loadLLVMModule :: FilePath -> IO LLVMModule
loadLLVMModule file = LLVMModule file <$> loadModule file

browseLLVMModule :: LLVMModule -> IO ()
browseLLVMModule (LLVMModule name m) = do
  putStrLn ("Module: " ++ name)
  putStrLn "Types:"
  showParts ppTypeDecl (modTypes m)
  putStrLn ""
  putStrLn "Globals:"
  showParts ppGlobal' (modGlobals m)
  putStrLn ""
  putStrLn "External references:"
  showParts ppDeclare (modDeclares m)
  putStrLn ""
  putStrLn "Definitions:"
  showParts ppDefine' (modDefines m)
  putStrLn ""
    where
      showParts pp xs = mapM_ (print . nest 2 . pp) xs
      ppGlobal' g =
        ppSymbol (globalSym g) <+> PP.char '=' <+>
        ppGlobalAttrs (globalAttrs g) <+>
        ppType (globalType g)
      ppDefine' d =
        ppMaybe ppLinkage (funLinkage (defAttrs d)) <+>
        ppType (defRetType d) <+>
        ppSymbol (defName d) <>
          ppArgList (defVarArgs d) (map (ppTyped ppIdent) (defArgs d)) <+>
        ppMaybe (\gc -> text "gc" <+> ppGC gc) (funGC (defAttrs d))

type Assign = (LLVMExpr, TypedTerm SAWCtx)

addrPlusOffset :: (Functor m, MonadIO m) =>
                  SBETerm sbe -> Offset
               -> Simulator sbe m (SBETerm sbe)
addrPlusOffset a o = do
  sbe <- gets symBE
  w <- ptrBitwidth <$> getDL
  ot <- liftSBE $ termInt sbe w (fromIntegral o)
  liftSBE $ applyTypedExpr sbe (PtrAdd a ot)

writeLLVMTerm :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                 DataLayout
              -> [SBETerm sbe]
              -> LLVMExpr
              -> SBETerm sbe
              -> Simulator sbe m ()
writeLLVMTerm dl args (Term e) t = do
  case e of
    Arg _ _ _ -> fail "Can't write to argument."
    Global s ty -> do
      addr <- evalExprInCC "writeLLVMTerm:Global" (SValSymbol s)
      store ty addr t (memTypeAlign dl ty)
    Deref ae ty -> do
      addr <- readLLVMTerm dl args ae
      store ty addr t (memTypeAlign dl ty)
    StructField ae si idx ty ->
      case siFieldOffset si idx of
        Just off -> do
          saddr <- readLLVMTermAddr dl args ae
          addr <- addrPlusOffset saddr off
          store ty t addr (memTypeAlign dl ty)
        Nothing ->
          fail $ "Struct field index " ++ show idx ++ " out of bounds"
    ReturnValue _ -> fail "Can't write to return value."

readLLVMTermAddr :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                    DataLayout -> [SBETerm sbe] -> LLVMExpr
                 -> Simulator sbe m (SBETerm sbe)
readLLVMTermAddr dl args (Term e) =
  case e of
    Arg _ _ _ -> fail "Can't read address of argument"
    Global s _ -> evalExprInCC "readLLVMTerm:Global" (SValSymbol s)
    Deref ae _ -> readLLVMTerm dl args ae
    StructField ae si idx _ ->
      case siFieldOffset si idx of
        Just off -> do
          saddr <- readLLVMTermAddr dl args ae
          addrPlusOffset saddr off
        Nothing ->
          fail $ "Struct field index " ++ show idx ++ " out of bounds"
    ReturnValue _ -> fail "Can't read address of return value"

readLLVMTerm :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                DataLayout -> [SBETerm sbe] -> LLVMExpr
             -> Simulator sbe m (SBETerm sbe)
readLLVMTerm dl args (Term e) =
  case e of
    Arg n _ _ -> return (args !! n)
    Global s ty -> do
      addr <- evalExprInCC "readLLVMTerm:Global" (SValSymbol s)
      load ty addr (memTypeAlign dl ty)
    Deref ae ty -> do
      addr <- readLLVMTerm dl args ae
      load ty addr (memTypeAlign dl ty)
    StructField ae si idx ty ->
      case siFieldOffset si idx of
        Just off -> do
          saddr <- readLLVMTermAddr dl args ae
          addr <- addrPlusOffset saddr off
          load ty addr (memTypeAlign dl ty)
        Nothing ->
          fail $ "Struct field index " ++ show idx ++ " out of bounds"
    ReturnValue _ -> do
      rslt <- getProgramReturnValue
      case rslt of
        (Just v) -> return v
        Nothing -> fail "Program did not return a value"

symexecLLVM :: BuiltinContext
            -> Options
            -> LLVMModule
            -> String
            -> [(String, SharedTerm SAWCtx)]
            -> [String]
            -> IO (TypedTerm SAWCtx)
symexecLLVM bic opts (LLVMModule file mdl) fname inputs outputs = do
  let sym = Symbol fname
      dl = parseDataLayout $ modDataLayout mdl
      sc = biSharedContext bic
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl sc
    (_warnings, cb) <- mkCodebase sbe dl mdl
    case lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ fname ++ "."
      Just md -> runSimulator cb sbe mem Nothing $ do
        setVerbosity (simVerbose opts)
        let mkAssign (s, tm) = do
              e <- failLeft $ liftIO $ parseLLVMExpr cb md s
              return (e, tm)
            isArg (Term (Arg _ _ _)) = True
            isArg _ = False
            multDefErr i = error $ "Multiple terms given for argument " ++
                                   show i ++ " in function " ++ fname
        assigns <- mapM mkAssign inputs
        let allocOne ty = do
              let aw = ptrBitwidth dl
              sz <- liftSBE (termInt sbe aw 1)
              malloc ty aw sz
        let (argAssigns, otherAssigns) = partition (isArg . fst) assigns
            argMap =
              Map.fromListWithKey
              (\i _ _ -> multDefErr i)
              [ (idx, (tp, tm)) | (Term (Arg idx _ tp), tm) <- argAssigns ]
        let rargs = [(i, resolveType cb ty) | (i, ty) <- sdArgs md]
        args <- forM (zip [0..] rargs) $ \(i, (_, ty)) ->
                  case (Map.lookup i argMap, ty) of
                    (Just v, _) -> return v
                    (Nothing, PtrType (MemType dty)) -> (ty,) <$> allocOne dty
                    _ -> fail $ "No binding for argument " ++ show i ++
                                " in function " ++ fname
        let argVals = map snd args
        let retReg = (,Ident "__SAWScript_rslt") <$> sdRetType md
        _ <- callDefine' False sym retReg args
        mapM_ (uncurry (writeLLVMTerm dl argVals)) otherAssigns
        run
        outexprs <- liftIO $ mapM (failLeft . parseLLVMExpr cb md) outputs
        outtms <- mapM (readLLVMTerm dl argVals) outexprs
        let bundle tms = case tms of
                           [t] -> return t
                           _ -> scTuple scLLVM tms
        liftIO (mkTypedTerm scLLVM =<< bundle outtms)


-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: SharedContext SAWCtx -> LLVMModule -> String -> LLVMSetup ()
            -> IO (TypedTerm SAWCtx)
extractLLVM sc (LLVMModule file mdl) func _setup = do
  let dl = parseDataLayout $ modDataLayout mdl
      sym = Symbol func
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl sc
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
           -> IO LLVMMethodSpecIR
verifyLLVM bic opts (LLVMModule _file mdl) func overrides setup = do
  let pos = fixPos -- TODO
      dl = parseDataLayout $ modDataLayout mdl
      sc = biSharedContext bic
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl sc
    (_warnings, cb) <- mkCodebase sbe dl mdl
    let ms0 = initLLVMMethodSpec pos cb func
        lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsTactic = Skip
                  , lsContext = scLLVM
                  , lsSimulate = True
                  }
    (_, lsctx) <- runStateT setup lsctx0
    let ms = lsSpec lsctx
    let vp = VerifyParams { vpCode = cb
                          , vpContext = scLLVM
                          , vpOpts = opts
                          , vpSpec = ms
                          , vpOver = overrides
                          }
    let verb = verbLevel (vpOpts vp)
    let overrideText =
          case overrides of
            [] -> ""
            irs -> " (overriding " ++ show (map specFunction irs) ++ ")"
    when (verb >= 2) $ putStrLn $ "Starting verification of " ++ show (specName ms)
    {-
    let configs = [ (bs, cl)
                  | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                  , cl <- bsRefEquivClasses bs
                  ] -}
    let lopts = Nothing -- FIXME
    when (lsSimulate lsctx) $ do
    -- forM_ configs $ \(bs,cl) -> do
      when (verb >= 3) $ do
        putStrLn $ "Executing " ++ show (specName ms)
      runSimulator cb sbe mem lopts $ do
        setVerbosity verb
        esd <- initializeVerification scLLVM ms
        res <- mkSpecVC scLLVM vp esd
        when (verb >= 3) $ liftIO $ do
          putStrLn "Verifying the following:"
          mapM_ (print . ppPathVC) res
        let prover :: ProofScript SAWCtx SV.SatResult
                   -> VerifyState
                   -> SharedTerm SAWCtx
                   -> IO ()
            prover script vs g = do
              glam <- bindAllExts scLLVM g
              let bsc = biSharedContext bic
              glam' <- scImport bsc glam
              tt <- mkTypedTerm bsc glam'
              r <- evalStateT script (ProofGoal Universal (vsVCName vs) tt)
              case r of
                SV.Unsat -> when (verb >= 3) $ putStrLn "Valid."
                SV.Sat val ->  showCexResults scLLVM ms vs [("x", val)] -- TODO: replace x with something
                SV.SatMulti vals -> showCexResults scLLVM ms vs vals
        case lsTactic lsctx of
          Skip -> liftIO $ putStrLn $
            "WARNING: skipping verification of " ++ show (specName ms)
          RunVerify script ->
            liftIO $ runValidation (prover script) vp scLLVM esd res
    if lsSimulate lsctx
       then putStrLn $ "Successfully verified " ++
                       show (specName ms) ++ overrideText
       else putStrLn $ "WARNING: skipping simulation of " ++ show (specName ms)
    return ms

showCexResults :: SharedContext SAWCtx
               -> LLVMMethodSpecIR
               -> VerifyState
               -> [(String, FiniteValue)]
               -> IO ()
showCexResults sc ms vs vals = do
  putStrLn $ "When verifying " ++ show (specName ms) ++ ":"
  putStrLn $ "Proof of " ++ vsVCName vs ++ " failed."
  putStrLn $ "Counterexample: "
  mapM_ (\(n, v) -> putStrLn ("  " ++ n ++ ": " ++ show v)) vals
  vsCounterexampleFn vs (cexEvalFn sc (map snd vals)) >>= print
  fail "Proof failed."

llvmPure :: LLVMSetup ()
llvmPure = return ()

type LLVMExprParser a = ParsecT String () IO a

failLeft :: (Monad m, Show s) => m (Either s a) -> m a
failLeft act = either (fail . show) return =<< act

parseLLVMExpr :: Codebase (SAWBackend SAWCtx)
              -> SymDefine (SharedTerm SAWCtx)
              -> String
              -> IO (Either ParseError LLVMExpr)
parseLLVMExpr cb fn str = runParserT (parseExpr <* eof) () "expr" str
  where
    args = [(i, resolveType cb ty) | (i, ty) <- sdArgs fn]
    numArgs = zipWith (\(i, ty) n -> (i, (n, ty))) args [(0::Int)..]
    parseExpr :: LLVMExprParser LLVMExpr
    parseExpr = choice
                [ parseDerefField
                , parseDeref
                , parseDirectField
                , parseAExpr
                ]
    parseAExpr = choice
                 [ parseReturn
                 , parseArgs
                 , parseVar
                 , parseParens
                 ]
    alphaUnder = choice [P.letter, P.char '_']
    parseIdent = (:) <$> alphaUnder <*> many (choice [alphaUnder, P.digit])
    parseVar = do
      s <- try parseIdent
      let nid = fromString s
      case lookup nid numArgs of
        Just (n, ty) -> return (Term (Arg n nid ty))
        Nothing ->
          case lookupSym (Symbol s) cb of
            Just (Left gb) ->
              return (Term (Global (CB.globalSym gb) (CB.globalType gb)))
            _ -> unexpected $ "Unknown variable: " ++ s
    parseParens = string "(" *> parseExpr <* string ")"
    parseReturn = do
      _ <- try (string "return")
      case sdRetType fn of
        Just ty -> return (Term (ReturnValue ty))
        Nothing ->
          unexpected "Function with void return type used with `return`."
    parseDeref = do
      _ <- string "*"
      e <- parseAExpr
      case lssTypeOfLLVMExpr e of
        PtrType (MemType ty) -> return (Term (Deref e ty))
        ty -> unexpected $
              "Attempting to apply * operation to non-pointer, of type " ++
              show (ppActualType ty)
    parseArgs :: LLVMExprParser LLVMExpr
    parseArgs = do
      _ <- try (string "args[")
      ns <- many1 digit
      e <- case readMaybe ns of
             Just (n :: Int)
               | n < length numArgs -> do
                 let (i, ty) = args !! n
                 return (Term (Arg n i ty))
               | otherwise ->
                 unexpected $ "Argument index too large: " ++ show n
             Nothing ->
               unexpected $ "Using `args` with non-numeric parameter: " ++ ns
      _ <- string "]"
      return e
    parseDirectField :: LLVMExprParser LLVMExpr
    parseDirectField = do
      e <- try (parseAExpr <* string ".")
      ns <- many1 digit
      case (lssTypeOfLLVMExpr e, readMaybe ns) of
        (StructType si, Just (n :: Int))
          | n < siFieldCount si -> do
            let ty = fiType (siFields si V.! n)
            return (Term (StructField e si n ty))
          | otherwise -> unexpected $ "Field out of range: " ++ show n
        (_, Nothing) -> unexpected $
          "Attempting to apply . operation to invalid field: " ++ ns
        (ty, Just _) ->
          unexpected $ "Attempting to apply . operation to non-struct: " ++
                       show (ppActualType ty)
    parseDerefField :: LLVMExprParser LLVMExpr
    parseDerefField = do
      re <- try (parseAExpr <* string "->")
      ns <- many1 digit
      case (lssTypeOfLLVMExpr re, readMaybe ns) of
        (PtrType (MemType sty@(StructType si)), Just (n :: Int))
          | n < siFieldCount si -> do
            let e = Term (Deref re sty)
                ty = fiType (siFields si V.! n)
            return (Term (StructField e si n ty))
          | otherwise -> unexpected $ "Field out of range: " ++ show n
        (_, Nothing) -> unexpected $
          "Attempting to apply -> operation to invalid field: " ++ ns
        (ty, Just _) ->
          unexpected $ "Attempting to apply -> operation to non-struct: " ++
                       show (ppActualType ty)

resolveType :: Codebase (SAWBackend SAWCtx) -> MemType -> MemType
resolveType cb (PtrType ty) = PtrType $ resolveSymType cb ty
resolveType _ ty = ty

resolveSymType :: Codebase (SAWBackend SAWCtx) -> SymType -> SymType
resolveSymType cb (MemType mt) = MemType $ resolveType cb mt
resolveSymType cb ty@(Alias i) =
  fromMaybe ty $ lookupAlias i where ?lc = cbLLVMContext cb
resolveSymType _ ty = ty

getLLVMExpr :: Monad m =>
               LLVMMethodSpecIR -> String
            -> m (LLVMExpr, MemType)
getLLVMExpr ms name = do
  case Map.lookup name (specLLVMExprNames ms) of
    -- TODO: maybe compute type differently?
    Just (_, expr) -> return (expr, lssTypeOfLLVMExpr expr)
    Nothing -> fail $ "LLVM name " ++ name ++ " has not been declared."

llvmInt :: Int -> MemType
llvmInt n = IntType n

llvmFloat :: MemType
llvmFloat = FloatType

llvmDouble :: MemType
llvmDouble = DoubleType

llvmArray :: Int -> MemType -> MemType
llvmArray n t = ArrayType n t

llvmNoSimulate :: LLVMSetup ()
llvmNoSimulate = modify (\s -> s { lsSimulate = False })

llvmVar :: BuiltinContext -> Options -> String -> MemType
        -> LLVMSetup (TypedTerm SAWCtx)
llvmVar bic _ name lty = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
  funcDef <- case lookupDefine func cb of
               Just fd -> return fd
               Nothing -> fail $ "Function " ++ show func ++ " not found."
  expr <- failLeft $ liftIO $ parseLLVMExpr cb funcDef name
  let expr' = updateLLVMExprType expr lty
  modify $ \st ->
    st { lsSpec = specAddVarDecl fixPos name expr' lty (lsSpec st) }
  let sc = biSharedContext bic
  Just ty <- liftIO $ logicTypeOfActual sc lty
  liftIO $ scLLVMValue sc ty name >>= mkTypedTerm sc

llvmPtr :: BuiltinContext -> Options -> String -> MemType
        -> LLVMSetup (TypedTerm SAWCtx)
llvmPtr bic _ name lty = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
      Just funcDef = lookupDefine func cb
  expr <- failLeft $ liftIO $ parseLLVMExpr cb funcDef name
  let pty = PtrType (MemType lty)
      expr' = updateLLVMExprType expr pty
      dexpr = Term (Deref expr' lty)
      dname = '*':name
  modify $ \st -> st { lsSpec = specAddVarDecl fixPos dname dexpr lty $
                                specAddVarDecl fixPos name expr' pty (lsSpec st) }
  let sc = biSharedContext bic
  Just dty <- liftIO $ logicTypeOfActual sc lty
  liftIO $ scLLVMValue sc dty dname >>= mkTypedTerm sc

llvmDeref :: BuiltinContext -> Options -> Value
          -> LLVMSetup (SharedTerm SAWCtx)
llvmDeref _bic _ _t = fail "llvm_deref not yet implemented"

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
llvmAssertEq _bic _ name t = do
  ms <- gets lsSpec
  (expr, _) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec = specAddLogicAssignment fixPos expr (mkLogicExpr t) ms }

llvmEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> LLVMSetup ()
llvmEnsureEq _ _ name t = do
  ms <- gets lsSpec
  (expr, _) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (Ensure fixPos expr (LogicE (mkLogicExpr t))) (lsSpec st) }

llvmModify :: BuiltinContext -> Options -> String
           -> LLVMSetup ()
llvmModify _ _ _name = fail "llvm_modify not implemented" {- do
  ms <- gets lsSpec
  (expr, ty) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (Modify expr ty) (lsSpec st) } -}

llvmReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmReturn _ _ t =
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand (Return (LogicE (mkLogicExpr t))) (lsSpec st) }

llvmVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SV.SatResult
                 -> LLVMSetup ()
llvmVerifyTactic _ _ script =
  modify $ \st -> st { lsTactic = RunVerify script }
