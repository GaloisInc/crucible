{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module SAWScript.Builtins where

import Control.Applicative
import Control.Lens
import Control.Monad.Error
import Control.Monad.State
import Data.Either (partitionEithers)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))


import qualified Verifier.Java.Codebase as JSS
import Verifier.Java.SAWBackend (javaModule)

import Verifier.SAW.BitBlast
import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.SBVParser as SBV
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.TypedAST hiding (instantiateVarList)

import qualified Verifier.SAW.Export.Yices as Y
import qualified Verifier.SAW.Export.SMT.Version1 as SMT1
import qualified Verifier.SAW.Export.SMT.Version2 as SMT2
import Verifier.SAW.Import.AIG

import qualified SAWScript.AST as SS

import SAWScript.Proof
import SAWScript.Utils
import qualified SAWScript.Value as SV

import qualified Data.ABC as ABC
import qualified Verinf.Symbolic.Lit.ABC_GIA as GIA

--import qualified Verinf.Symbolic as BE

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

withBE :: (forall s . ABC.GIA s -> IO a) -> IO a
withBE f = do
  ABC.withNewGraph ABC.giaNetwork f

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
  let eqs = map (mkIdent preludeName) [ "eq_Bool"
                                      , "get_single"
                                      , "bvNat_bvToNat"
                                      , "equalNat_bv"
                                      ]
      defs = map (mkIdent (moduleName javaModule))
                 [ "ecJoin", "ecJoin768", "ecSplit", "ecSplit768"
                 , "ecExtend", "longExtend"
                 ] ++
             map (mkIdent preludeName)
                 [ "splitLittleEndian", "joinLittleEndian" ]
  rs1 <- concat <$> traverse (defRewrites sc) defs
  rs2 <- scEqsRewriteRules sc eqs
  basics <- basic_ss sc
  let ss = addRules (rs1 ++ rs2) basics
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
      ABC.writeAiger f (ABC.Network be (ABC.bvToList (flattenBValue bterm)))

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
satABC :: SharedContext s -> ProofScript s (SV.SatResult s)
satABC sc = StateT $ \t -> withBE $ \be -> do
  t' <- prepForExport sc t
  let (args, _) = asLambdaList t'
      argNames = map fst args
      argTys = map snd args
  shapes <- mapM parseShape argTys
  mbterm <- bitBlast be t'
  case mbterm of
    Right bterm -> do
      case bterm of
        BBool l -> do
          satRes <- ABC.checkSat be l
          case satRes of
            ABC.Unsat -> (SV.Unsat,) <$> scApplyPreludeFalse sc
            ABC.Sat cex -> do
              r <- liftCexBB sc shapes cex
              case r of
                Left err -> fail $ "Can't parse counterexample: " ++ err
                Right [tm] -> (SV.Sat (SV.evaluate sc tm),) <$>
                              scApplyPreludeTrue sc
                Right tms ->
                  fail . unlines $
                  "Proof failed with multi-argument counterexample: " :
                  map show (zip argNames tms)
        _ -> fail "Can't prove non-boolean term."
    Left err -> fail $ "Can't bitblast: " ++ err

satYices :: SharedContext s -> ProofScript s (SV.SatResult s)
satYices sc = StateT $ \t -> withBE $ \be -> do
  t' <- prepForExport sc t
  let (args, _) = asLambdaList t'
      argNames = map fst args
      argTys = map snd args
  shapes <- mapM parseShape argTys
  let ws = SMT1.qf_aufbv_WriterState sc "sawscript"
  ws' <- execStateT (SMT1.writeFormula t') ws
  mapM_ (print . (text "WARNING:" <+>) . SMT1.ppWarning)
        (map (fmap scPrettyTermDoc) (ws' ^. SMT1.warnings))
  res <- Y.yices Nothing (SMT1.smtScript ws')
  case res of
    Y.YUnsat -> (SV.Unsat,) <$> scApplyPreludeFalse sc
    Y.YSat m -> do
      r <- liftCexMapYices sc m
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right [(_n, tm)] -> (SV.Sat (SV.evaluate sc tm),) <$>
                            scApplyPreludeTrue sc
        Right tms ->
          fail . unlines $
          "Proof failed with multi-argument counterexample: " :
          map show (zip argNames tms)
    Y.YUnknown -> fail "ABC returned Unknown for SAT query."

satAIG :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satAIG sc path = StateT $ \t -> do
  writeAIG sc path t
  (SV.Unsat,) <$> scApplyPreludeFalse sc

satExtCore :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satExtCore sc path = StateT $ \t -> do
  writeCore path t
  (SV.Unsat,) <$> scApplyPreludeFalse sc

satSMTLib1 :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satSMTLib1 sc path = StateT $ \t -> do
  writeSMTLib1 sc path t
  (SV.Unsat,) <$> scApplyPreludeFalse sc

satSMTLib2 :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satSMTLib2 sc path = StateT $ \t -> do
  writeSMTLib2 sc path t
  (SV.Unsat,) <$> scApplyPreludeFalse sc

liftCexBB :: SharedContext s -> [BShape] -> [Bool]
          -> IO (Either String [SharedTerm s])
liftCexBB sc shapes bs =
  case liftCounterExamples shapes bs of
    Left err -> return (Left err)
    Right bvals -> do
      ts <- mapM (scSharedTerm sc . liftConcreteBValue) bvals
      return (Right ts)

liftCexYices :: SharedContext s -> Y.YVal
             -> IO (Either String (SharedTerm s))
liftCexYices sc yv =
  case yv of
    Y.YVar "true" -> Right <$> scBool sc True
    Y.YVar "false" -> Right <$> scBool sc False
    Y.YVal bv ->
      Right <$> scBvConst sc (fromIntegral (Y.width bv)) (Y.val bv)
    _ -> return $ Left $
         "Can't translate non-bitvector Yices value: " ++ show yv

liftCexMapYices :: SharedContext s -> Map.Map String Y.YVal
             -> IO (Either String [(String, SharedTerm s)])
liftCexMapYices sc m = do
  let (ns, vs) = unzip (Map.toList m)
  (errs, tms) <- partitionEithers <$> mapM (liftCexYices sc) vs
  return $ case errs of
    [] -> Right $ zip ns tms
    _ -> Left $ unlines errs

-- | Logically negate a term @t@, which must be a boolean term
-- (possibly surrounded by one or more lambdas).
scNegate :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scNegate sc t =
  case asLambda t of
    Just (s, ty, body) -> scLambda sc s ty =<< scNegate sc body
    Nothing -> scNot sc t

-- | Translate a @SharedTerm@ representing a theorem for input to the
-- given validity-checking script and attempt to prove it.
provePrim :: SharedContext s -> ProofScript s (SV.SatResult s)
          -> SharedTerm s -> IO (SV.ProofResult s)
provePrim sc script t = do
  t' <- scNegate sc t
  (r, _) <- runStateT script t'
  return (SV.flipSatResult r)

-- | FIXME: change return type so that we can return the witnesses.
satPrim :: SharedContext s -> ProofScript s (SV.SatResult s) -> SharedTerm s
        -> IO (SV.SatResult s)
satPrim _sc script t = do
  (r, _) <- runStateT script t
  return r

rewritePrim :: SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewritePrim sc ss t = rewriteSharedTerm sc ss t

addsimp :: SharedContext s -> Theorem s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp _sc (Theorem t) ss = addRule (ruleOfPred t) ss

equalPrim :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
equalPrim t1 t2 = mkSC $ \sc -> equal sc [] t1 t2

-- evaluate :: (a :: sort 0) -> Term -> a;
evaluate :: (Ident -> Value) -> () -> SharedTerm s -> Value
evaluate global _ = evalSharedTerm global

myPrint :: () -> Value -> SC s ()
myPrint _ (VString s) = mkSC $ const (putStrLn s)
myPrint _ v = mkSC $ const (print v)

print_type :: SharedContext s -> SharedTerm s -> IO ()
print_type sc t = scTypeOf sc t >>= print

fixPos :: Pos
fixPos = PosInternal "FIXME"

bindExts :: SharedContext s
         -> [SharedTerm s]
         -> SharedTerm s
         -> IO (SharedTerm s)
bindExts sc args body = do
  types <- mapM (scTypeOf sc) args
  let is = mapMaybe extIdx args
  unless (length types == length is) $
    fail "argument isn't external input"
  locals <- mapM (scLocalVar sc . fst) ([0..] `zip` reverse types)
  body' <- scInstantiateExt sc (Map.fromList (is `zip` reverse locals)) body
  scLambdaList sc (names `zip` types) body'
    where names = map ('x':) (map show ([0..] :: [Int]))
          extIdx (STApp _ (FTermF (ExtCns ec))) = Just (ecVarIndex ec)
          extIdx _ = Nothing

caseProofResultPrim :: SharedContext s -> ProofResult s
                    -> SV.Value s -> SV.Value s
                    -> IO (SV.Value s)
caseProofResultPrim sc pr vValid vInvalid = do
  case pr of
    Valid -> return vValid
    Invalid t ->
      case vInvalid of
        SV.VFunTerm f -> return (f t)
        SV.VLambda f -> f (SV.evaluate sc t) Nothing
        SV.VFun f -> return (f (SV.evaluate sc t))
        _ -> fail $ "Invalid case of caseProofResultPrim isn't a function: " ++
                    show vInvalid


caseSatResultPrim :: SharedContext s -> SatResult s
                  -> SV.Value s -> SV.Value s
                  -> IO (SV.Value s)
caseSatResultPrim sc sr vUnsat vSat = do
  case sr of
    Unsat -> return vUnsat
    Sat t ->
      case vSat of
        SV.VFunTerm f -> return (f t)
        SV.VLambda f -> f (SV.evaluate sc t) Nothing
        SV.VFun f -> return (f (SV.evaluate sc t))
        _ -> fail $ "Sat case of caseSatResultPrim isn't a function: " ++
                    show vSat
