{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.Builtins where

import Control.Applicative
import Control.Exception (bracket)
import Control.Lens
import Control.Monad.Error
import Control.Monad.State
import Data.List (sort)
import Data.List.Split
import Data.IORef
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read (readMaybe)

import qualified Language.JVM.Common as JP

import Verinf.Symbolic.Lit.ABC
import qualified Verinf.Symbolic.Lit.ABC_GIA as GIA

import qualified Text.LLVM as LLVM
import qualified Verifier.LLVM.Backend as L
import qualified Verifier.LLVM.Codebase as L
import qualified Verifier.LLVM.Backend.SAW as LSAW
import qualified Verifier.LLVM.Simulator as L

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Simulator as JSS
import qualified Verifier.Java.SAWBackend as JSS2

import Verifier.SAW.BitBlast
import Verifier.SAW.Conversion hiding (asCtor)
import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.SBVParser as SBV
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.TypedAST hiding (instantiateVarList)

import qualified Verifier.SAW.Export.SMT.Version1 as SMT1
import qualified Verifier.SAW.Export.SMT.Version2 as SMT2
import Verifier.SAW.Import.AIG

import qualified SAWScript.AST as SS
import qualified SAWScript.CongruenceClosure as CC
import SAWScript.JavaExpr
import SAWScript.MethodSpec
import SAWScript.MethodSpecIR
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import qualified SAWScript.Value as SS

import qualified Verinf.Symbolic as BE
import Verinf.Utils.LogMonad

data BuiltinContext = BuiltinContext { biSharedContext :: SharedContext SAWCtx
                                     , biJavaCodebase  :: JSS.Codebase
                                     }

-- bitSequence :: {n} Integer -> [n]
bitSequence :: SS.Type -> Integer -> Prim.BitVector
bitSequence (SS.TyCon (SS.NumCon w) []) x = Prim.BV (fromInteger w) x
bitSequence t x = error $ "bitSequence " ++ show (t, x)

--topReturn :: (a :: sort 0) -> a -> TopLevel a;
topReturn :: () -> Value -> SC s Value
topReturn _ = return

--topBind :: (a b :: sort 0) -> TopLevel a -> (a -> TopLevel b) -> TopLevel b;
topBind :: () -> () -> SC s Value -> (Value -> SC s Value) -> SC s Value
topBind _ _ = (>>=)

definePrim :: SharedContext s -> String -> SharedTerm s -> IO (SharedTerm s)
definePrim sc name rhs = scConstant sc ident rhs
  where ident = mkIdent (moduleName (scModule sc)) name

-- TODO: Add argument for uninterpreted-function map
readSBV :: SharedContext s -> SS.Type -> FilePath -> IO (SharedTerm s)
readSBV sc ty path =
    do pgm <- SBV.loadSBV path
       let ty' = importTyp (SBV.typOf pgm)
       when (ty /= ty') $
            fail $ "read_sbv: expected " ++ showTyp ty ++ ", found " ++ showTyp ty'
       SBV.parseSBVPgm sc (\_ _ -> Nothing) pgm
    where
      showTyp :: SS.Type -> String
      showTyp = show . SS.pretty False
      importTyp :: SBV.Typ -> SS.Type
      importTyp typ =
        case typ of
          SBV.TBool -> SS.TyCon SS.BoolCon []
          SBV.TFun t1 t2 -> SS.TyCon SS.FunCon [importTyp t1, importTyp t2]
          SBV.TVec n t -> SS.TyCon SS.ArrayCon [SS.TyCon (SS.NumCon n) [], importTyp t]
          SBV.TTuple ts -> SS.TyCon (SS.TupleCon (toInteger (length ts))) (map importTyp ts)
          SBV.TRecord bs -> SS.TyRecord (fmap importTyp (Map.fromList bs))

withBE :: (BE.BitEngine BE.Lit -> IO a) -> IO a
withBE f = do
  be <- BE.createBitEngine
  r <- f be
  BE.beFree be
  return r

-- | Read an AIG file representing a theorem or an arbitrary function
-- and represent its contents as a @SharedTerm@ lambda term. This is
-- inefficient but semantically correct.
readAIGPrim :: SharedContext s -> FilePath -> IO (SharedTerm s)
readAIGPrim sc f = do
  et <- withReadAiger f $ \ntk -> do
    outputLits <- GIA.networkOutputs ntk
    inputLits <- GIA.networkInputs ntk
    inLen <- scNat sc (fromIntegral (SV.length inputLits))
    outLen <- scNat sc (fromIntegral (SV.length outputLits))
    boolType <- scBoolType sc
    inType <- scVecType sc inLen boolType
    outType <- scVecType sc outLen boolType
    runErrorT $
      translateNetwork sc ntk outputLits [("x", inType)] outType
  case et of
    Left err -> fail $ "Reading AIG failed: " ++ err
    Right t -> return t

-- | Apply some rewrite rules before exporting, to ensure that terms
-- are within the language subset supported by formats such as SMT-Lib
-- QF_AUFBV or AIG.
prepForExport :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
prepForExport sc t = do
  ss <- scSimpset sc []  [mkIdent (moduleName preludeModule) "get_single"] []
  rewriteSharedTerm sc ss t

-- | Write a @SharedTerm@ representing a theorem or an arbitrary
-- function to an AIG file.
writeAIG :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeAIG sc f t = withBE $ \be -> do
  t' <- prepForExport sc t
  mbterm <- bitBlast be t'
  case mbterm of
    Left msg ->
      fail $ "Can't bitblast term: " ++ msg
    Right bterm -> do
      ins <- BE.beInputLits be
      BE.beWriteAigerV be f ins (flattenBValue bterm)

-- | Write a @SharedTerm@ representing a theorem to an SMT-Lib version
-- 1 file.
writeSMTLib1 :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeSMTLib1 sc f t = do
  -- TODO: better benchmark name than "sawscript"?
  t' <- prepForExport sc t
  let ws = SMT1.qf_aufbv_WriterState sc "sawscript"
  ws' <- execStateT (SMT1.writeFormula t') ws
  mapM_ (print . (text "WARNING:" <+>) . SMT1.ppWarning)
        (map (fmap scPrettyTermDoc) (ws' ^. SMT1.warnings))
  writeFile f (SMT1.render ws')

-- | Write a @SharedTerm@ representing a theorem to an SMT-Lib version
-- 2 file.
writeSMTLib2 :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeSMTLib2 sc f t = do
  t' <- prepForExport sc t
  let ws = SMT2.qf_aufbv_WriterState sc
  ws' <- execStateT (SMT2.assert t') ws
  mapM_ (print . (text "WARNING:" <+>) . SMT2.ppWarning)
        (map (fmap scPrettyTermDoc) (ws' ^. SMT2.warnings))
  writeFile f (SMT2.render ws')

writeCore :: FilePath -> SharedTerm s -> IO ()
writeCore path t = writeFile path (scWriteExternal t)

readCore :: SharedContext s -> FilePath -> IO (SharedTerm s)
readCore sc path = scReadExternal sc =<< readFile path

printGoal :: ProofScript s ()
printGoal = StateT $ \goal -> do
  putStrLn (scPrettyTerm goal)
  return ((), goal)

unfoldGoal :: SharedContext s -> [String] -> ProofScript s ()
unfoldGoal sc names = StateT $ \goal -> do
  let ids = map (mkIdent (moduleName (scModule sc))) names
  goal' <- scUnfoldConstants sc ids goal
  return ((), goal')

simplifyGoal :: SharedContext s -> Simpset (SharedTerm s) -> ProofScript s ()
simplifyGoal sc ss = StateT $ \goal -> do
  goal' <- rewriteSharedTerm sc ss goal
  return ((), goal')

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext s -> ProofScript s ProofResult
satABC sc = StateT $ \t -> withBE $ \be -> do
  t' <- prepForExport sc t
  mbterm <- bitBlast be t'
  case (mbterm, BE.beCheckSat be) of
    (Right bterm, Just chk) -> do
      case bterm of
        BBool l -> do
          satRes <- chk l
          case satRes of
            BE.UnSat -> (,) () <$> scApplyPreludeFalse sc
            BE.Sat _ -> (,) () <$> scApplyPreludeTrue sc
            _ -> fail "ABC returned Unknown for SAT query."
        _ -> fail "Can't prove non-boolean term."
    (_, Nothing) -> fail "Backend does not support SAT checking."
    (Left err, _) -> fail $ "Can't bitblast: " ++ err

-- | Logically negate a term @t@, which must be a boolean term
-- (possibly surrounded by one or more lambdas).
scNegate :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scNegate sc t =
  case asLambda t of
    Just (s, ty, body) -> scLambda sc s ty =<< scNegate sc body
    Nothing -> scNot sc t

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- validity using ABC.
provePrim :: SharedContext s -> ProofScript s ProofResult
          -> SharedTerm s -> IO (Theorem s)
provePrim sc script t = do
  t' <- scNegate sc t
  (_, r) <- runStateT script t'
  case asCtor r of
    Just ("Prelude.True", []) -> fail "prove: invalid"
    Just ("Prelude.False", []) -> return (Theorem t)
    _ -> fail "prove: unknown result"

-- | FIXME: change return type so that we can return the witnesses.
satPrim :: SharedContext s -> ProofScript s ProofResult -> SharedTerm s
        -> IO String
satPrim _sc script t = do
  (_, r) <- runStateT script t
  return $
    case asCtor r of
      Just ("Prelude.True", []) -> "sat"
      Just ("Prelude.False", []) -> "unsat"
      _ -> "unknown"

rewritePrim :: SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewritePrim sc ss t = rewriteSharedTerm sc ss t

addsimp :: SharedContext s -> Theorem s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp _sc (Theorem t) ss = addRule (ruleOfPred t) ss

basic_ss :: SharedContext s -> IO (Simpset (SharedTerm s))
basic_ss sc = do
  rs1 <- concat <$> traverse defRewrites defs
  rs2 <- scEqsRewriteRules sc eqs
  return $ addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
  where
    eqs = map (mkIdent preludeName)
      ["get_single", "get_bvAnd", "get_bvOr", "get_bvXor", "get_bvNot",
       "not_not", "get_slice", "bvAddZeroL", "bvAddZeroR"]
    defs = map (mkIdent preludeName)
      ["not", "and", "or", "xor", "boolEq", "ite", "addNat", "mulNat", "compareNat", "finSucc"]
    procs = bvConversions ++ natConversions ++ finConversions ++ vecConversions
    defRewrites ident =
      case findDef (scModule sc) ident of
        Nothing -> return []
        Just def -> scDefRewriteRules sc def

equalPrim :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
equalPrim t1 t2 = mkSC $ \sc -> equal sc t1 t2

-- evaluate :: (a :: sort 0) -> Term -> a;
evaluate :: (Ident -> Value) -> () -> SharedTerm s -> Value
evaluate global _ = evalSharedTerm global

myPrint :: () -> Value -> SC s ()
myPrint _ (VString s) = mkSC $ const (putStrLn s)
myPrint _ v = mkSC $ const (print v)

print_type :: SharedContext s -> SharedTerm s -> IO ()
print_type sc t = scTypeOf sc t >>= print

type LLVMSetup s a = IO a

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: SharedContext SAWCtx -> FilePath -> String -> LLVMSetup s ()
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

bindExts :: SharedContext s
         -> [SharedTerm s]
         -> SharedTerm s
         -> IO (SharedTerm s)
bindExts sc args body = do
  types <- mapM (scTypeOf sc) args
  let is = mapMaybe extIdx args
  unless (length types == length is) $
    fail "argument isn't external input"
  locals <- mapM (uncurry (scLocalVar sc)) ([0..] `zip` reverse types)
  body' <- scInstantiateExt sc (Map.fromList (is `zip` reverse locals)) body
  scLambdaList sc (names `zip` types) body'
    where names = map ('x':) (map show ([0..] :: [Int]))
          extIdx (STApp _ (FTermF (ExtCns ec))) = Just (ecVarIndex ec)
          extIdx _ = Nothing

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

fixPos :: Pos
fixPos = PosInternal "FIXME"

extractJava :: BuiltinContext -> Options -> String -> String
            -> JavaSetup ()
            -> IO (SharedTerm SAWCtx)
extractJava bic opts cname mname _setup = do
  let cname' = JP.dotsToSlashes cname
      sc = biSharedContext bic
      cb = biJavaCodebase bic
  cls <- lookupClass cb fixPos cname'
  (_, meth) <- findMethod cb fixPos mname cls
  argsRef <- newIORef []
  bracket BE.createBitEngine BE.beFree $ \be -> do
    let fl = JSS.defaultSimFlags { JSS.alwaysBitBlastBranchTerms = True }
    sbe <- JSS2.sawBackend sc (Just argsRef) be
    JSS.runSimulator cb sbe JSS.defaultSEH (Just fl) $ do
      setVerbosity 0
      args <- mapM (freshJavaArg sbe) (JSS.methodParameterTypes meth)
      rslt <- JSS.execStaticMethod cname' (JSS.methodKey meth) args
      dt <- case rslt of
              Nothing -> fail "No return value from JSS."
              Just (JSS.IValue t) -> return t
              Just (JSS.LValue t) -> return t
              _ -> fail "Unimplemented result type from JSS."
      liftIO $ do
        argsRev <- readIORef argsRef
        bindExts sc (reverse argsRev) dt

freshJavaArg :: MonadIO m =>
                JSS.Backend sbe
             -> JSS.Type
             -> m (JSS.AtomicValue d f (JSS.SBETerm sbe) (JSS.SBETerm sbe) r)
--freshJavaArg sbe JSS.BooleanType =
freshJavaArg sbe JSS.ByteType = liftIO (JSS.IValue <$> JSS.freshByte sbe)
--freshJavaArg sbe JSS.CharType =
--freshJavaArg sbe JSS.ShortType =
freshJavaArg sbe JSS.IntType = liftIO (JSS.IValue <$> JSS.freshInt sbe)
freshJavaArg sbe JSS.LongType = liftIO (JSS.LValue <$> JSS.freshLong sbe)
freshJavaArg _ _ = fail "Only byte, int, and long arguments are supported for now."

verifyJava :: BuiltinContext -> Options -> String -> String
           -> [MethodSpecIR]
           -> JavaSetup ()
           -> IO (MethodSpecIR)
verifyJava bic opts cname mname overrides setup = do
  let pos = fixPos -- TODO
      cb = biJavaCodebase bic
  sc0 <- mkSharedContext preludeModule
  ss <- basic_ss sc0
  let (jsc :: SharedContext JSSCtx) = sc0 -- rewritingSharedContext sc0 ss
  be <- createBitEngine
  backend <- JSS2.sawBackend jsc Nothing be
  ms0 <- initMethodSpec pos cb cname mname
  let jsctx0 = JavaSetupState {
                 jsSpec = ms0
               , jsContext = jsc
               }
  (_, jsctx) <- runStateT setup jsctx0
  let ms = jsSpec jsctx
  let vp = VerifyParams {
             vpCode = cb
           , vpContext = jsc
           , vpOpts = opts
           , vpSpec = ms
           , vpOver = overrides
           }
  let verb = simVerbose (vpOpts vp)
  when (verb >= 2) $ putStrLn $ "Starting verification of " ++ specName ms
  let configs = [ (bs, cl)
                | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                , cl <- bsRefEquivClasses bs
                ]
  forM_ configs $ \(bs,cl) -> do
    when (verb >= 3) $ do
      putStrLn $ "Executing " ++ specName ms ++
                 " at PC " ++ show (bsLoc bs) ++ "."
    JSS.runDefSimulator cb backend $ do
      esd <- initializeVerification jsc ms bs cl
      let isExtCns (STApp _ (FTermF (ExtCns e))) = True
          isExtCns _ = False
          initialExts =
            sort . filter isExtCns . map snd . esdInitialAssignments $ esd
      res <- mkSpecVC jsc vp esd
      when (verb >= 3) $ liftIO $ do
        putStrLn "Verifying the following:"
        mapM_ (print . ppPathVC) res
      let prover vs script g = do
            glam <- bindExts jsc initialExts g
            glam' <- scImport (biSharedContext bic) glam
            Theorem thm <- provePrim (biSharedContext bic) script glam'
            when (verb >= 3) $ putStrLn $ "Proved: " ++ show thm
      liftIO $ runValidation prover vp jsc esd res
  BE.beFree be
  return ms

parseJavaExpr :: JSS.Codebase -> JSS.Class -> JSS.Method -> String
              -> IO JavaExpr
parseJavaExpr cb cls meth = parseParts . reverse . splitOn "."
  where parseParts [] = fail "empty Java expression"
        parseParts [s] =
          case s of
            "this" -> return (thisJavaExpr cls)
            ('a':'r':'g':'s':'[':rest) -> do
              let num = fst (break (==']') rest)
              case readMaybe num of
                Just (n :: Int) -> do
                  let i = JSS.localIndexOfParameter meth n
                      mlv = JSS.lookupLocalVariableByIdx meth 0 i
                  case mlv of
                    Nothing -> error $ "parameter doesn't exist: " ++ show n
                    Just lv -> return (CC.Term (Local s i (JSS.localType lv)))
                Nothing -> fail $ "bad Java expression syntax: " ++ s
            _ -> do
              let mlv = JSS.lookupLocalVariableByName meth 0 s
              case mlv of
                Nothing -> error $ "local doesn't exist: " ++ s
                Just lv -> return (CC.Term (Local s i ty))
                  where i = JSS.localIdx lv
                        ty = JSS.localType lv
        parseParts (f:rest) = do
          e <- parseParts rest
          let jt = jssTypeOfJavaExpr e
              pos = fixPos -- TODO
          fid <- findField cb pos jt f
          return (CC.Term (InstanceField e fid))

exportJSSType :: SS.Value s -> JSS.Type
exportJSSType (SS.VCtorApp "Java.IntType" []) = JSS.IntType
exportJSSType (SS.VCtorApp "Java.Longype" []) = JSS.LongType
exportJSSType (SS.VCtorApp "Java.ArrayType" [_, ety]) =
  JSS.ArrayType (exportJSSType ety)
exportJSSType v = error $ "Can't translate to Java type: " ++ show v

exportJavaType :: SS.Value s -> JavaActualType
exportJavaType (SS.VCtorApp "Java.IntType" []) = PrimitiveType JSS.IntType
exportJavaType (SS.VCtorApp "Java.Longype" []) = PrimitiveType JSS.LongType
exportJavaType (SS.VCtorApp "Java.ArrayType" [SS.VInteger n, ety]) =
  ArrayInstance (fromIntegral n) (exportJSSType ety)
exportJavaType v = error $ "Can't translate to Java type: " ++ show v

javaVar :: BuiltinContext -> Options -> String -> SS.Value SAWCtx
        -> JavaSetup ()
javaVar bic _ name t@(SS.VCtorApp _ _) = do
  jsState <- get
  let ms = jsSpec jsState
      cls = specMethodClass ms
      meth = specMethod ms
  exp <- liftIO $ parseJavaExpr (biJavaCodebase bic) cls meth name
  ty <- return (exportJavaType t)
  -- TODO: check that exp and ty match
  modify $ \st -> st { jsSpec = specAddVarDecl name exp ty (jsSpec st) }
  -- TODO: Could return (java_value name) for convenience? (within SAWScript context)
javaVar _ _ _ _ = fail "java_var called with invalid type argument"

{-
javaMayAlias :: BuiltinContext -> Options -> SharedTerm SAWCtx
             -> JavaSetup ()
javaMayAlias bic _ t@(STApp _ (FTermF (ArrayValue _ es))) = do
  case sequence (map asStringLit (V.toList es)) of
    Just names -> do
      let cb = biJavaCodebase bic
      exprs <- liftIO $ mapM (parseJavaExpr cb) names
      modify $ specAddAliasSet exprs
    Nothing -> fail "non-string arguments passed to java_may_alias"
javaMayAlias _ _ _ = fail "java_may_alias called with invalid type argument"
-}

javaAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> JavaSetup ()
javaAssert _ _ v =
  modify $ \st ->
    st { jsSpec = specAddBehaviorCommand (AssertPred fixPos (mkLogicExpr v)) (jsSpec st) }

getJavaExpr :: Monad m =>
               MethodSpecIR -> String
            -> m (JavaExpr, JSS.Type)
getJavaExpr ms name = do
  case Map.lookup name (specJavaExprNames ms) of
    Just exp -> return (exp, jssTypeOfJavaExpr exp)
    Nothing -> fail $ "Java name " ++ name ++ " has not been declared."

javaAssertEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
           -> JavaSetup ()
javaAssertEq bic _ name t = do
  ms <- gets jsSpec
  (exp, ty) <- liftIO $ getJavaExpr ms name
  fail "javaAssertEq"

javaEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> JavaSetup ()
javaEnsureEq bic _ name t = do
  ms <- gets jsSpec
  (exp, ty) <- liftIO $ getJavaExpr ms name
  let cmd = case (CC.unTerm exp, ty) of
              (_, JSS.ArrayType _) -> EnsureArray fixPos exp le
              (InstanceField r f, _) -> EnsureInstanceField fixPos r f (LE le)
              _ -> error "invalid java_ensure command"
      le = mkLogicExpr t
  modify $ \st -> st { jsSpec = specAddBehaviorCommand cmd ms }

javaModify :: BuiltinContext -> Options -> String
           -> JavaSetup ()
javaModify bic _ name = do
  ms <- gets jsSpec
  (exp, _) <- liftIO $ getJavaExpr ms name
  let mty = Map.lookup exp (bsActualTypeMap (specBehaviors ms))
  let cmd = case (CC.unTerm exp, mty) of
              (_, Just ty@(ArrayInstance _ _)) -> ModifyArray exp ty
              (InstanceField r f, _) -> ModifyInstanceField r f
              _ -> error "invalid java_modify command"
  modify $ \st -> st { jsSpec = specAddBehaviorCommand cmd ms }

javaReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> JavaSetup ()
javaReturn _ _ t =
  modify $ \st ->
    st { jsSpec = specAddBehaviorCommand (Return (LE (mkLogicExpr t))) (jsSpec st) }

javaVerifyTactic :: BuiltinContext -> Options -> ProofScript SAWCtx ProofResult
                 -> JavaSetup ()
javaVerifyTactic _ _ script =
  modify $ \st -> st { jsSpec = specSetVerifyTactic script (jsSpec st) }

verifyLLVM :: BuiltinContext -> Options -> String -> String
           -> [SS.LLVMMethodSpecIR s]
           -> SS.LLVMSetup s ()
           -> IO (SS.LLVMMethodSpecIR s)
verifyLLVM bic opts file func overrides setup = do
  let pos = fixPos -- TODO
      sc = biSharedContext bic
  mdl <- L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
      sym = L.Symbol func
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- LSAW.createSAWBackend' be dl
    (_warnings, cb) <- L.mkCodebase sbe dl mdl
    (_, ms) <- runStateT setup =<< initLLVMMethodSpec pos cb mdl sym
    fail "verifyLLVM"
    return ms

initLLVMMethodSpec = fail "initLLVMMethodSpec"

llvmVar :: BuiltinContext -> Options -> String -> SS.Value s
        -> SS.LLVMSetup s ()
llvmVar = fail "llvmVar"

llvmAssert :: BuiltinContext -> Options -> SharedTerm s
           -> SS.LLVMSetup s ()
llvmAssert = fail "llvmAssert"

llvmAssertEq :: BuiltinContext -> Options -> String -> SharedTerm s
           -> SS.LLVMSetup s ()
llvmAssertEq = fail "llvmAssertEq"

llvmEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm s
           -> SS.LLVMSetup s ()
llvmEnsureEq = fail "llvmEnsureEq"

llvmModify :: BuiltinContext -> Options -> String
           -> SS.LLVMSetup s ()
llvmModify = fail "llvmEnsureEq"

llvmReturn :: BuiltinContext -> Options -> SharedTerm s
           -> SS.LLVMSetup s ()
llvmReturn _ _ v = fail "llvmReturn"

llvmVerifyTactic :: BuiltinContext -> Options -> ProofScript s ProofResult
                 -> SS.LLVMSetup s ()
llvmVerifyTactic = fail "llvmVerifyTactic"
