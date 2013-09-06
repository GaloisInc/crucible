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
import Data.List.Split
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read (readMaybe)

import qualified Language.JVM.Common as JP

import Verinf.Symbolic.Lit.ABC_GIA

import qualified Text.LLVM as LLVM
import qualified Verifier.LLVM.Backend as L
import qualified Verifier.LLVM.Codebase as L
import qualified Verifier.LLVM.Backend.SAW as LSAW
import qualified Verifier.LLVM.Simulator as L

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Simulator as JSS
import qualified Verifier.Java.WordBackend as JSS

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
import SAWScript.Utils
import qualified SAWScript.Value as SS

import qualified Verinf.Symbolic as BE
import Verinf.Utils.LogMonad

data BuiltinContext s = BuiltinContext { biSharedContext :: SharedContext s
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

{-
unLambda :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
unLambda sc (STApp _ (Lambda (PVar x _ _) ty tm)) = do
  arg <- scFreshGlobal sc x ty
  instantiateVar sc 0 arg tm >>= unLambda sc
unLambda _ tm = return tm
-}

-- | Read an AIG file representing a theorem or an arbitrary function
-- and represent its contents as a @SharedTerm@ lambda term. This is
-- inefficient but semantically correct.
readAIGPrim :: SharedContext s -> FilePath -> IO (SharedTerm s)
readAIGPrim sc f = do
  et <- withReadAiger f $ \ntk -> do
    outputLits <- networkOutputs ntk
    inputLits <- networkInputs ntk
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

printGoal :: SS.ProofScript s ()
printGoal = StateT $ \goal -> do
  putStrLn (scPrettyTerm goal)
  return ((), goal)

unfoldGoal :: SharedContext s -> [String] -> SS.ProofScript s ()
unfoldGoal sc names = StateT $ \goal -> do
  let ids = map (mkIdent (moduleName (scModule sc))) names
  goal' <- scUnfoldConstants sc ids goal
  return ((), goal')

simplifyGoal :: SharedContext s -> Simpset (SharedTerm s) -> SS.ProofScript s ()
simplifyGoal sc ss = StateT $ \goal -> do
  goal' <- rewriteSharedTerm sc ss goal
  return ((), goal')

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext s -> SS.ProofScript s SS.ProofResult
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
provePrim :: SharedContext s -> SS.ProofScript s SS.ProofResult
          -> SharedTerm s -> IO (SS.Theorem s)
provePrim sc script t = do
  t' <- scNegate sc t
  (_, r) <- runStateT script t'
  case asCtor r of
    Just ("Prelude.True", []) -> fail "prove: invalid"
    Just ("Prelude.False", []) -> return (SS.Theorem t)
    _ -> fail "prove: unknown result"

-- | FIXME: change return type so that we can return the witnesses.
satPrim :: SharedContext s -> SS.ProofScript s SS.ProofResult -> SharedTerm s
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

addsimp :: SharedContext s -> SS.Theorem s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp _sc (SS.Theorem t) ss = addRule (ruleOfPred t) ss

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

equal :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
equal sc (STApp _ (Lambda (PVar x1 _ _) ty1 tm1)) (STApp _ (Lambda (PVar _ _ _) ty2 tm2)) =
  case (asBitvectorType ty1, asBitvectorType ty2) of
    (Just n1, Just n2) -> do
      unless (n1 == n2) $
        fail $ "Arguments have different sizes: " ++
               show n1 ++ " and " ++ show n2
      eqBody <- equal sc tm1 tm2
      scLambda sc x1 ty1 eqBody
    (_, _) ->
        fail $ "Incompatible function arguments. Types are " ++
               show ty1 ++ " and " ++ show ty2
equal sc tm1@(STApp _ (FTermF _)) tm2@(STApp _ (FTermF _)) = do
    ty1 <- scTypeOf sc tm1
    ty2 <- scTypeOf sc tm2
    case (asBitvectorType ty1, asBitvectorType ty2) of
      (Just n1, Just n2) -> do
        unless (n1 == n2) $ fail "Types have different sizes."
        n1t <- scNat sc n1
        scBvEq sc n1t tm1 tm2
      (_, _) ->
        fail $ "Incompatible non-lambda terms. Types are " ++
               show ty1 ++ " and " ++ show ty2
equal sc t1 t2 = do
  ty1 <- scTypeOf sc t1
  ty2 <- scTypeOf sc t2
  fail $ "Incompatible terms. Types are " ++ show ty1 ++ " and " ++ show ty2

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
extractLLVM :: SharedContext s -> FilePath -> String -> LLVMSetup s ()
            -> IO (SharedTerm s)
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
          Just bt -> undefined
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

extractJava :: BuiltinContext s -> Options -> String -> String
            -> SS.JavaSetup s ()
            -> IO (SharedTerm s)
extractJava bic opts cname mname _setup = do
  let cname' = JP.dotsToSlashes cname
      sc = biSharedContext bic
      cb = biJavaCodebase bic
  cls <- lookupClass cb fixPos cname'
  (_, meth) <- findMethod cb fixPos mname cls
  oc <- BE.mkOpCache
  bracket BE.createBitEngine BE.beFree $ \be -> do
    de <- BE.mkConstantFoldingDagEngine
    sms <- JSS.mkSymbolicMonadState oc be de
    let fl  = JSS.defaultSimFlags { JSS.alwaysBitBlastBranchTerms = True }
        sbe = JSS.symbolicBackend sms
    JSS.runSimulator cb sbe JSS.defaultSEH (Just fl) $ do
      setVerbosity 0
      args <- mapM (freshJavaArg sbe) (JSS.methodParameterTypes meth)
      rslt <- JSS.execStaticMethod cname' (JSS.methodKey meth) args
      dt <- case rslt of
              Nothing -> fail "No return value from JSS."
              Just (JSS.IValue t) -> return t
              Just (JSS.LValue t) -> return t
              _ -> fail "Unimplemented result type from JSS."
      et <- liftIO $ parseVerinfViaAIG sc de dt
      case et of
        Left err -> fail $ "Failed to extract Java model: " ++ err
        Right t -> return t

verifyJava :: BuiltinContext s -> Options -> String -> String -> SS.JavaSetup s ()
           -> IO (MethodSpecIR s)
verifyJava bic opts cname mname setup = do
  let pos = fixPos -- TODO
      sc = biSharedContext bic
      cb = biJavaCodebase bic
  (_, ms) <- runStateT setup =<< initMethodSpec pos cb cname mname
  print ms
  let vp = VerifyParams {
             vpCode = cb
           , vpContext = sc
           , vpOpts = opts
           , vpSpec = ms
           , vpOver = [] -- TODO
           , vpRules = [] -- TODO
           , vpEnabledRules = Set.empty -- TODO
           }
  validateMethodSpec vp (runValidation vp)
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

exportJavaType :: SS.Value s -> JavaActualType
exportJavaType (SS.VCtorApp "Java.IntType" []) = PrimitiveType JSS.IntType
exportJavaType v = error $ "Can't translate to Java type: " ++ show v

javaVar :: BuiltinContext s -> Options -> String -> SS.Value s
        -> SS.JavaSetup s ()
javaVar bic _ name t@(SS.VCtorApp _ _) = do
  ms <- get
  let cls = specMethodClass ms
      meth = specMethod ms
  exp <- liftIO $ parseJavaExpr (biJavaCodebase bic) cls meth name
  ty <- return (exportJavaType t)
  modify $ specAddVarDecl exp ty
javaVar _ _ _ _ = fail "java_var called with invalid type argument"

{-
javaMayAlias :: BuiltinContext s -> Options -> SharedTerm s
             -> SS.JavaSetup s ()
javaMayAlias bic _ t@(STApp _ (FTermF (ArrayValue _ es))) = do
  case sequence (map asStringLit (V.toList es)) of
    Just names -> do
      let cb = biJavaCodebase bic
      exprs <- liftIO $ mapM (parseJavaExpr cb) names
      modify $ specAddAliasSet exprs
    Nothing -> fail "non-string arguments passed to java_may_alias"
javaMayAlias _ _ _ = fail "java_may_alias called with invalid type argument"
-}

javaReturn :: BuiltinContext s -> Options -> SharedTerm s
           -> SS.JavaSetup s ()
javaReturn _ _ v = modify $ specAddBehaviorCommand (Return (LE v))

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
