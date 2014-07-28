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
import Data.Foldable (foldl')
import Data.List (isPrefixOf)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector.Storable as SV
import System.Exit
import System.Process
import Text.PrettyPrint.Leijen hiding ((<$>))


import qualified Verifier.Java.Codebase as JSS
import Verifier.Java.SAWBackend (javaModule)
import Verifier.LLVM.Backend.SAW (llvmModule)

import Verifier.SAW.BitBlast
import Verifier.SAW.Evaluator hiding (applyAll)
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

import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import Verifier.SAW.Simulator.Value (applyAll)

import qualified Data.ABC as ABC
import qualified Verinf.Symbolic.Lit.ABC_GIA as GIA

import Data.ABC (aigNetwork)
import qualified Data.ABC.GIA as GIA
import qualified Data.AIG as AIG


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
             map (mkIdent (moduleName llvmModule))
                 [ "trunc31" ] ++
             map (mkIdent preludeName)
                 [ "splitLittleEndian", "joinLittleEndian", "finEq" ]
  rs1 <- concat <$> traverse (defRewrites sc) defs
  rs2 <- scEqsRewriteRules sc eqs
  basics <- basic_ss sc
  let ss = addRules (rs1 ++ rs2) basics
  rewriteSharedTerm sc ss t

-- TODO: this belongs elsewhere
asAIGType :: SharedContext s -> SharedTerm s -> IO [SharedTerm s]
asAIGType sc t = do
  t' <- scWhnf sc t
  case t' of
    (asPi -> Just (_, t1, t2)) -> (t1 :) <$> asAIGType sc t2
    (asBoolType -> Just ())    -> return []
    (asVecType -> Just _)      -> return []
    (asTupleType -> Just _)    -> return []
    (asRecordType -> Just _)   -> return []
    _                          -> fail $ "invalid AIG type: " ++ show t'

-- TODO: the following sequence should probably go into BitBlast
bitBlastTerm :: AIG.IsAIG l g =>
                g s
             -> SharedContext t -> SharedTerm t -> IO (BBSim.LitVector (l s))
bitBlastTerm be sc t = do
  ty <- scTypeOf sc t
  argTs <- asAIGType sc ty
  shapes <- traverse (BBSim.parseShape sc) argTs
  vars <- traverse (BBSim.newVars' be) shapes
  bval <- BBSim.bitBlastBasic be (scModule sc) t
  bval' <- applyAll bval vars
  BBSim.flattenBValue bval'

-- | Write a @SharedTerm@ representing a theorem or an arbitrary
-- function to an AIG file.
writeAIG :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeAIG sc f t = withBE $ \be -> do
  ls <- bitBlastTerm be sc t
  ABC.writeAiger f (ABC.Network be (ABC.bvToList ls))
  return ()

writeCNF :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeCNF sc f t = withBE $ \be -> do
  ls <- bitBlastTerm be sc t
  case AIG.bvToList ls of
    [l] -> do
      _ <- GIA.writeCNF be l f
      return ()
    _ -> fail "writeCNF: non-boolean term"

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

assumeValid :: ProofScript s (SV.ProofResult s)
assumeValid = StateT $ \goal -> do
  putStrLn $ "WARNING: assuming goal " ++ goalName goal ++ " is valid"
  return (SV.Valid, goal)

assumeUnsat :: ProofScript s (SV.SatResult s)
assumeUnsat = StateT $ \goal -> do
  putStrLn $ "WARNING: assuming goal " ++ goalName goal ++ " is unsat"
  return (SV.Unsat, goal)

printGoal :: ProofScript s ()
printGoal = StateT $ \goal -> do
  putStrLn (scPrettyTerm (goalTerm goal))
  return ((), goal)

unfoldGoal :: SharedContext s -> [String] -> ProofScript s ()
unfoldGoal sc names = StateT $ \goal -> do
  let ids = map (mkIdent (moduleName (scModule sc))) names
  goalTerm' <- scUnfoldConstants sc ids (goalTerm goal)
  return ((), goal { goalTerm = goalTerm' })

simplifyGoal :: SharedContext s -> Simpset (SharedTerm s) -> ProofScript s ()
simplifyGoal sc ss = StateT $ \goal -> do
  goalTerm' <- rewriteSharedTerm sc ss (goalTerm goal)
  return ((), goal { goalTerm = goalTerm' })

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABCold :: SharedContext s -> ProofScript s (SV.SatResult s)
satABCold sc = StateT $ \g -> withBE $ \be -> do
  let t = goalTerm g
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
            ABC.Unsat -> do
              ft <- scApplyPreludeFalse sc
              return (SV.Unsat, g { goalTerm = ft })
            ABC.Sat cex -> do
              r <- liftCexBB sc shapes cex
              tt <- scApplyPreludeTrue sc
              case r of
                Left err -> fail $ "Can't parse counterexample: " ++ err
                Right [tm] ->
                  return (SV.Sat (SV.evaluate sc tm), g { goalTerm = tt })
                Right tms -> do
                  let vs = map (SV.evaluate sc) tms
                  return (SV.SatMulti (zip argNames vs), g { goalTerm = tt })
        _ -> fail "Can't prove non-boolean term."
    Left err -> fail $ "Can't bitblast: " ++ err

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext s -> ProofScript s (SV.SatResult s)
satABC sc = StateT $ \g -> AIG.withNewGraph aigNetwork $ \be -> do
  let t = goalTerm g
      eqs = map (mkIdent preludeName) [ "eq_Vec", "eq_Fin", "eq_Bool" ]
  rs <- scEqsRewriteRules sc eqs
  basics <- basic_ss sc
  let ss = addRules rs basics
  t' <- rewriteSharedTerm sc ss t
  let (args, _) = asLambdaList t'
      argNames = map fst args
  -- putStrLn "Simulating..."
  (shapes, lit) <- BBSim.bitBlast be sc t'
  -- putStrLn "Checking..."
  satRes <- AIG.checkSat be lit
  case satRes of
    AIG.Unsat -> do
      -- putStrLn "UNSAT"
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = ft })
    AIG.Sat cex -> do
      -- putStrLn "SAT"
      r <- liftCexBB sc (map convertShape shapes) cex
      tt <- scApplyPreludeTrue sc
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right [tm] ->
          return (SV.Sat (SV.evaluate sc tm), g { goalTerm = tt })
        Right tms -> do
          let vs = map (SV.evaluate sc) tms
          return (SV.SatMulti (zip argNames vs), g { goalTerm = tt })

convertShape :: BBSim.BShape -> BShape --FIXME: temporary
convertShape BBSim.BoolShape = BoolShape
convertShape (BBSim.VecShape n x) = VecShape n (convertShape x)
convertShape (BBSim.TupleShape xs) = TupleShape (map convertShape xs)
convertShape (BBSim.RecShape xm) = RecShape (fmap convertShape xm)

satYices :: SharedContext s -> ProofScript s (SV.SatResult s)
satYices sc = StateT $ \g -> do
  let t = goalTerm g
  t' <- prepForExport sc t
  let ws = SMT1.qf_aufbv_WriterState sc "sawscript"
  ws' <- execStateT (SMT1.writeFormula t') ws
  mapM_ (print . (text "WARNING:" <+>) . SMT1.ppWarning)
        (map (fmap scPrettyTermDoc) (ws' ^. SMT1.warnings))
  res <- Y.yices Nothing (SMT1.smtScript ws')
  case res of
    Y.YUnsat -> do
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = ft })
    Y.YSat m -> do
      r <- liftCexMapYices sc m
      tt <- scApplyPreludeTrue sc
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right [(_n, tm)] -> do
          return (SV.Sat (SV.evaluate sc tm), g { goalTerm = tt })
        Right tms -> do
          let vs = map (\(n, v) -> (n, SV.evaluate sc v)) tms
          return (SV.SatMulti vs, g { goalTerm = tt })
    Y.YUnknown -> fail "ABC returned Unknown for SAT query."

satExternalCNF :: SharedContext s -> String -> [String]
               -> ProofScript s (SV.SatResult s)
satExternalCNF sc execName args = StateT $ \g -> withBE $ \be -> do
  let cnfName = goalName g ++ ".cnf" 
      args' = map replaceFileName args
      replaceFileName "%f" = cnfName
      replaceFileName a = a
      t = goalTerm g
      argNames = map fst (fst (asLambdaList t))
  (shapes, l) <- BBSim.bitBlast be sc t
  varMap <- GIA.writeCNF be l cnfName
  (_ec, out, err) <- readProcessWithExitCode execName args' ""
  unless (null err) $
    print $ "Standard error from SAT solver: " ++ err
  let ls = lines out
      sls = filter ("s " `isPrefixOf`) ls
      vls = filter ("v " `isPrefixOf`) ls
  case (sls, vls) of
    (["s SATISFIABLE"], _) -> do
      let vs :: [Int]
          vs = concatMap (map read . tail . words) vls
          varToPair n | n < 0 = (n, False)
                      | otherwise = (n, True)
          assgnMap = Map.fromList (map varToPair vs)
          val = map (\v -> Map.findWithDefault False v assgnMap) varMap
      r <- liftCexBB sc (map convertShape shapes) val
      tt <- scApplyPreludeTrue sc
      case r of
        Left msg -> fail $ "Can't parse counterexample: " ++ msg
        Right [tm] ->
          return (SV.Sat (SV.evaluate sc tm), g { goalTerm = tt })
        Right tms -> do
          let vals = map (SV.evaluate sc) tms
          return (SV.SatMulti (zip argNames vals), g { goalTerm = tt })
    (["s UNSATISFIABLE"], []) -> do
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = ft })
    _ -> fail $ "Unexpected result from SAT solver:\n" ++ out

satAIG :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satAIG sc path = StateT $ \g -> do
  writeAIG sc ((path ++ goalName g) ++ ".aig") (goalTerm g)
  ft <- liftIO $ scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = ft })

satCNF :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satCNF sc path = StateT $ \g -> do
  writeCNF sc ((path ++ goalName g) ++ ".cnf") (goalTerm g)
  ft <- liftIO $ scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = ft })

satExtCore :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satExtCore sc path = StateT $ \g -> do
  writeCore ((path ++ goalName g) ++ ".extcore") (goalTerm g)
  ft <- liftIO $ scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = ft })

satSMTLib1 :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satSMTLib1 sc path = StateT $ \g -> do
  writeSMTLib1 sc ((path ++ goalName g) ++ ".smt") (goalTerm g)
  ft <- liftIO $ scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = ft })

satSMTLib2 :: SharedContext s -> FilePath -> ProofScript s (SV.SatResult s)
satSMTLib2 sc path = StateT $ \g -> do
  writeSMTLib2 sc ((path ++ goalName g) ++ ".smt2") (goalTerm g)
  ft <- liftIO $ scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = ft })

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
  (r, _) <- runStateT script (ProofGoal "prove" t')
  return (SV.flipSatResult r)

provePrintPrim :: SharedContext s -> ProofScript s (SV.SatResult s)
               -> SharedTerm s -> IO (Theorem s)
provePrintPrim sc script t = do
  t' <- scNegate sc t
  (r, _) <- runStateT script (ProofGoal "prove" t')
  case r of
    SV.Unsat -> putStrLn "Valid" >> return (Theorem t)
    _ -> fail (show (SV.flipSatResult r))

satPrim :: SharedContext s -> ProofScript s (SV.SatResult s) -> SharedTerm s
        -> IO (SV.SatResult s)
satPrim _sc script t = do
  (r, _) <- runStateT script (ProofGoal "sat" t)
  return r

satPrintPrim :: SharedContext s -> ProofScript s (SV.SatResult s)
             -> SharedTerm s -> IO ()
satPrintPrim _sc script t = do
  (r, _) <- runStateT script (ProofGoal "sat" t)
  print r

rewritePrim :: SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewritePrim sc ss t = rewriteSharedTerm sc ss t

addsimp :: SharedContext s -> Theorem s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp _sc (Theorem t) ss = addRule (ruleOfPred t) ss

addsimp' :: SharedContext s -> SharedTerm s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp' _sc t ss = addRule (ruleOfPred t) ss

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
      names = mapMaybe extName args
  unless (length types == length is && length types == length names) $
    fail "argument isn't external input"
  locals <- mapM (scLocalVar sc . fst) ([0..] `zip` reverse types)
  body' <- scInstantiateExt sc (Map.fromList (is `zip` reverse locals)) body
  scLambdaList sc (names `zip` types) body'
    where extIdx (STApp _ (FTermF (ExtCns ec))) = Just (ecVarIndex ec)
          extIdx _ = Nothing
          extName (STApp _ (FTermF (ExtCns ec))) = Just (ecName ec)
          extName _ = Nothing

bindAllExts :: SharedContext s
            -> SharedTerm s
            -> IO (SharedTerm s)
bindAllExts sc body@(STApp _ tf) = do
  bindExts sc (Set.toAscList args) body
    where args = snd $ foldl' getExtCns (Set.empty, Set.empty) tf
          getExtCns (is, a) (STApp idx _) | Set.member idx is = (is, a)
          getExtCns (is, a) t@(STApp idx (FTermF (ExtCns _))) =
            (Set.insert idx is, Set.insert t a)
          getExtCns (is, a) (STApp idx tf') =
            foldl' getExtCns (Set.insert idx is, a) tf'

-- | Apply the given SharedTerm to the given values, and evaluate to a
-- final value.
cexEvalFn :: SharedContext s -> [SV.Value SAWCtx] -> SharedTerm s
          -> IO Value
cexEvalFn sc args tm = do
  args' <- mapM (SV.exportSharedTerm sc) args
  let argMap = Map.fromList (zip [0..] args')
      eval = evalGlobal (scModule sc) preludePrims
  tm' <- scInstantiateExt sc argMap tm
  --ty <- scTypeCheck sc tm'
  --putStrLn $ "Type of cex eval term: " ++ show ty
  return $ evalSharedTerm eval tm'

toValueCase :: (SV.IsValue s b) =>
               SharedContext s
            -> (SharedContext s -> b -> SV.Value s -> SV.Value s -> IO (SV.Value s))
            -> SV.Value s
toValueCase sc prim =
  SV.VFun $ \b ->
  SV.VFun $ \v1 ->
  SV.VLambda $ \v2 _ ->
  prim sc (SV.fromValue b) v1 v2

caseProofResultPrim :: SharedContext s -> SV.ProofResult s
                    -> SV.Value s -> SV.Value s
                    -> IO (SV.Value s)
caseProofResultPrim sc pr vValid vInvalid = do
  case pr of
    SV.Valid -> return vValid
    SV.Invalid v -> SV.applyValue sc vInvalid v
    SV.InvalidMulti _ -> fail $ "multi-value counter-example"


caseSatResultPrim :: SharedContext s -> SV.SatResult s
                  -> SV.Value s -> SV.Value s
                  -> IO (SV.Value s)
caseSatResultPrim sc sr vUnsat vSat = do
  case sr of
    SV.Unsat -> return vUnsat
    SV.Sat v -> SV.applyValue sc vSat v
    SV.SatMulti _ -> fail $ "multi-value satisfying assignment"
