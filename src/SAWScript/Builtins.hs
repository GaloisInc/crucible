{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
module SAWScript.Builtins where

import Control.Applicative
import Control.Exception (bracket)
import Control.Lens
import Control.Monad.Error
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))

import qualified Language.JVM.Common as JP

import Verinf.Symbolic.Lit.ABC_GIA

import qualified Text.LLVM as LLVM
import qualified Verifier.LLVM.AST as L
import qualified Verifier.LLVM.Backend as L
import qualified Verifier.LLVM.Codebase as L
import qualified Verifier.LLVM.SAWBackend as LSAW
--import qualified Verifier.LLVM.BitBlastBackend as LBit
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
import SAWScript.Options
import SAWScript.Utils

import qualified Verinf.Symbolic as BE
import Verinf.Utils.LogMonad

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
    inType <- scBitvector sc (fromIntegral (SV.length inputLits))
    outType <- scBitvector sc (fromIntegral (SV.length outputLits))
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

type ProofScript a = a --FIXME
type ProofResult = () --FIXME

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext s -> ProofScript ProofResult -> SharedTerm s -> IO (SharedTerm s)
satABC sc _script t = withBE $ \be -> do
  t' <- prepForExport sc t
  mbterm <- bitBlast be t'
  case (mbterm, BE.beCheckSat be) of
    (Right bterm, Just chk) -> do
      case bterm of
        BBool l -> do
          satRes <- chk l
          case satRes of
            BE.UnSat -> scApplyPreludeFalse sc
            BE.Sat _ -> scApplyPreludeTrue sc
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
provePrim :: SharedContext s -> ProofScript ProofResult -> SharedTerm s -> IO String
provePrim sc script t = do
  t' <- scNegate sc t
  r <- satABC sc script t'
  return $
    case asCtor r of
      Just ("Prelude.True", []) -> "invalid"
      Just ("Prelude.False", []) -> "valid"
      _ -> "unknown"

satPrim :: SharedContext s -> ProofScript ProofResult -> SharedTerm s -> IO String
satPrim sc script t = do
  r <- satABC sc script t
  return $
    case asCtor r of
      Just ("Prelude.True", []) -> "sat"
      Just ("Prelude.False", []) -> "unsat"
      _ -> "unknown"

-- TODO: Replace () with Simpset argument.
rewritePrim :: SharedContext s -> () -> SharedTerm s -> IO (SharedTerm s)
rewritePrim sc _ t = do
  rs1 <- concat <$> traverse defRewrites defs
  rs2 <- scEqsRewriteRules sc eqs
  let simpset = addConvs procs (addRules (rs1 ++ rs2) emptySimpset)
  rewriteSharedTerm sc simpset t
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

type LLVMSetup a = a --FIXME

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: SharedContext s -> FilePath -> String -> LLVMSetup () -> IO (SharedTerm s)
extractLLVM sc file func _setup = do
  mdl <- L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
      mg = L.defaultMemGeom dl
      sym = L.Symbol func
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- LSAW.createSAWBackend' be dl mg
    cb <- L.mkCodebase sbe dl mdl
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

type JavaSetup a = a -- FIXME

extractJava :: SharedContext s -> Options -> String -> String -> JavaSetup () -> IO (SharedTerm s)
extractJava sc opts cname mname _setup = do
  cb <- JSS.loadCodebase (jarList opts) (classPath opts)
  let cname' = JP.dotsToSlashes cname
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

-- Java lookup functions {{{1

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists. Class name should be in slash-separated form.
lookupClass :: JSS.Codebase -> Pos -> String -> IO JSS.Class
lookupClass cb pos nm = do
  maybeCl <- JSS.tryLookupClass cb nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ JSS.slashesToDots nm ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException pos msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: JSS.Codebase -> Pos -> String -> JSS.Class -> IO (JSS.Class, JSS.Method)
findMethod cb pos nm initClass = impl initClass
  where javaClassName = JSS.slashesToDots (JSS.className initClass)
        methodMatches m = JSS.methodName m == nm && not (JSS.methodIsAbstract m)
        impl cl =
          case filter methodMatches (JSS.classMethods cl) of
            [] -> do
              case JSS.superClass cl of
                Nothing ->
                  let msg = ftext $ "Could not find method " ++ nm
                              ++ " in class " ++ javaClassName ++ "."
                      res = "Please check that the class and method are correct."
                   in throwIOExecException pos msg res
                Just superName ->
                  impl =<< lookupClass cb pos superName
            [method] -> return (cl,method)
            _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                             ++ " is ambiguous.  SAWScript currently requires that "
                             ++ "method names are unique."
                     res = "Please rename the Java method so that it is unique."
                  in throwIOExecException pos (ftext msg) res
