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
import Data.List (isPrefixOf, sortBy)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import System.Directory
import System.IO
import System.Process
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read


import qualified Verifier.Java.Codebase as JSS
import Verifier.Java.SAWBackend (javaModule)
import Verifier.LLVM.Backend.SAW (llvmModule)

import Verifier.SAW.Constant
import Verifier.SAW.ExternalFormat
import qualified Verifier.SAW.BitBlast as Old
import Verifier.SAW.FiniteValue (FiniteType(..), FiniteValue(..), scFiniteValue)
import Verifier.SAW.Evaluator hiding (applyAll)
import Verifier.SAW.Prelude
import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.TypedAST hiding (instantiateVarList)

import qualified Verifier.SAW.Export.Yices as Y
import qualified Verifier.SAW.Export.SMT.Version1 as SMT1
import qualified Verifier.SAW.Export.SMT.Version2 as SMT2

import qualified SAWScript.SBVParser as SBV
import SAWScript.ImportAIG

import qualified SAWScript.AST as SS

import SAWScript.Proof
import SAWScript.Utils
import qualified SAWScript.Value as SV

import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.Simulator.SBV as SBVSim

import qualified Data.ABC as ABC
import qualified Verinf.Symbolic.Lit.ABC_GIA as GIA

import qualified Data.SBV as SBV
import Data.SBV.Internals

import Data.ABC (aigNetwork)
import qualified Data.ABC.GIA as GIA
import qualified Data.AIG as AIG

import qualified Cryptol.TypeCheck.AST as C

import qualified Data.SBV.Bridge.Boolector as Boolector
import qualified Data.SBV.Bridge.Z3 as Z3
import qualified Data.SBV.Bridge.CVC4 as CVC4
import qualified Data.SBV.Bridge.Yices as Yices
import qualified Data.SBV.Bridge.MathSAT as MathSAT
import Data.SBV (modelExists, satWith, SMTConfig)

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

definePrim :: SharedContext s -> String -> SV.TypedTerm s -> IO (SV.TypedTerm s)
definePrim sc name (SV.TypedTerm schema rhs) = SV.TypedTerm schema <$> scConstant sc ident rhs
  where ident = mkIdent (moduleName (scModule sc)) name

sbvUninterpreted :: SharedContext s -> String -> SharedTerm s -> IO (Uninterp s)
sbvUninterpreted _ s t = return $ Uninterp (s, t)

readSBV :: SharedContext s -> FilePath -> [Uninterp s] -> IO (SV.TypedTerm s)
readSBV sc path unintlst =
    do pgm <- SBV.loadSBV path
       let schema = C.Forall [] [] (toCType (SBV.typOf pgm))
       trm <- SBV.parseSBVPgm sc (\s _ -> Map.lookup s unintmap) pgm
       return (SV.TypedTerm schema trm)
    where
      unintmap = Map.fromList $ map getUninterp unintlst

      toCType :: SBV.Typ -> C.Type
      toCType typ =
        case typ of
          SBV.TBool      -> C.tBit
          SBV.TFun t1 t2 -> C.tFun (toCType t1) (toCType t2)
          SBV.TVec n t   -> C.tSeq (C.tNum n) (toCType t)
          SBV.TTuple ts  -> C.tTuple (map toCType ts)
          SBV.TRecord bs -> C.tRec [ (C.Name n, toCType t) | (n, t) <- bs ]

withBE :: (forall s . ABC.GIA s -> IO a) -> IO a
withBE f = do
  ABC.withNewGraph ABC.giaNetwork f

-- | Read an AIG file representing a theorem or an arbitrary function
-- and represent its contents as a @SharedTerm@ lambda term. This is
-- inefficient but semantically correct.
readAIGPrim :: SharedContext s -> FilePath -> IO (SV.TypedTerm s)
readAIGPrim sc f = do
  exists <- doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
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
    Right t -> SV.mkTypedTerm sc t

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

-- | Write a @SharedTerm@ representing a theorem or an arbitrary
-- function to an AIG file.
writeAIG :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeAIG sc f t = withBE $ \be -> do
  ls <- BBSim.bitBlastTerm be sc t
  ABC.writeAiger f (ABC.Network be (ABC.bvToList ls))
  return ()

writeCNF :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeCNF sc f t = withBE $ \be -> do
  ls <- BBSim.bitBlastTerm be sc t
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

readCore :: SharedContext s -> FilePath -> IO (SV.TypedTerm s)
readCore sc path = SV.mkTypedTerm sc =<< scReadExternal sc =<< readFile path

assumeValid :: ProofScript s SV.ProofResult
assumeValid = StateT $ \goal -> do
  putStrLn $ "WARNING: assuming goal " ++ goalName goal ++ " is valid"
  return (SV.Valid, goal)

assumeUnsat :: ProofScript s SV.SatResult
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
satABCold :: SharedContext s -> ProofScript s SV.SatResult
satABCold sc = StateT $ \g -> withBE $ \be -> do
  let t = goalTerm g
  t' <- prepForExport sc t
  let (args, _) = asLambdaList t'
      argNames = map fst args
      argTys = map snd args
  shapes <- mapM Old.parseShape argTys
  mbterm <- Old.bitBlast be t'
  case mbterm of
    Right bterm -> do
      case bterm of
        Old.BBool l -> do
          satRes <- ABC.checkSat be l
          case satRes of
            ABC.Unsat -> do
              ft <- scApplyPreludeFalse sc
              return (SV.Unsat, g { goalTerm = ft })
            ABC.Sat cex -> do
              let r = liftCexBB shapes cex
              tt <- scApplyPreludeTrue sc
              case r of
                Left err -> fail $ "Can't parse counterexample: " ++ err
                Right [v] ->
                  return (SV.Sat v, g { goalTerm = tt })
                Right vs -> do
                  return (SV.SatMulti (zip argNames vs), g { goalTerm = tt })
        _ -> fail "Can't prove non-boolean term."
    Left err -> fail $ "Can't bitblast: " ++ err

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext s -> ProofScript s SV.SatResult
satABC sc = StateT $ \g -> AIG.withNewGraph aigNetwork $ \be -> do
  let t = goalTerm g
  let (args, _) = asLambdaList t
      argNames = map fst args
  -- putStrLn "Simulating..."
  (shapes, lit) <- BBSim.bitBlast be sc t
  -- putStrLn "Checking..."
  satRes <- AIG.checkSat be lit
  case satRes of
    AIG.Unsat -> do
      -- putStrLn "UNSAT"
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = ft })
    AIG.Sat cex -> do
      -- putStrLn "SAT"
      let r = liftCexBB shapes cex
      tt <- scApplyPreludeTrue sc
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right [v] ->
          return (SV.Sat v, g { goalTerm = tt })
        Right vs -> do
          return (SV.SatMulti (zip argNames vs), g { goalTerm = tt })

{-
satYices :: SharedContext s -> ProofScript s SV.SatResult
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
-}

parseDimacsSolution :: [Int]    -- ^ The list of CNF variables to return
                    -> [String] -- ^ The value lines from the solver
                    -> [Bool]
parseDimacsSolution vars ls = map lkup vars
  where
    vs :: [Int]
    vs = concatMap (filter (/= 0) . mapMaybe readMaybe . tail . words) ls
    varToPair n | n < 0 = (-n, False)
                | otherwise = (n, True)
    assgnMap = Map.fromList (map varToPair vs)
    lkup v = Map.findWithDefault False v assgnMap

satExternalCNF :: SharedContext s -> String -> [String]
               -> ProofScript s SV.SatResult
satExternalCNF sc execName args = StateT $ \g -> withBE $ \be -> do
  let cnfName = goalName g ++ ".cnf" 
      t = goalTerm g
      argNames = map fst (fst (asLambdaList t))
  (path, fh) <- openTempFile "." cnfName
  hClose fh -- Yuck. TODO: allow writeCNF et al. to work on handles.
  let args' = map replaceFileName args
      replaceFileName "%f" = path
      replaceFileName a = a
  (shapes, l) <- BBSim.bitBlast be sc t
  vars <- GIA.writeCNF be l path
  (_ec, out, err) <- readProcessWithExitCode execName args' ""
  removeFile path
  unless (null err) $
    print $ unlines ["Standard error from SAT solver:", err]
  let ls = lines out
      sls = filter ("s " `isPrefixOf`) ls
      vls = filter ("v " `isPrefixOf`) ls
  case (sls, vls) of
    (["s SATISFIABLE"], _) -> do
      let bs = parseDimacsSolution vars vls
      let r = liftCexBB shapes bs
      tt <- scApplyPreludeTrue sc
      case r of
        Left msg -> fail $ "Can't parse counterexample: " ++ msg
        Right [v] ->
          return (SV.Sat v, g { goalTerm = tt })
        Right vs -> do
          return (SV.SatMulti (zip argNames vs), g { goalTerm = tt })
    (["s UNSATISFIABLE"], []) -> do
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = ft })
    _ -> fail $ "Unexpected result from SAT solver:\n" ++ out

unsatResult :: SharedContext s -> ProofGoal s
            -> IO (SV.SatResult, ProofGoal s)
unsatResult sc g = do
  ft <- scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = ft })  

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using SBV. (Currently ignores satisfying assignments.)
satSBV :: SMTConfig -> SharedContext s -> ProofScript s SV.SatResult
satSBV conf sc = StateT $ \g -> do
  let t = goalTerm g
      eqs = map (mkIdent preludeName) [ "eq_Vec", "eq_Fin", "eq_Bool" ]
  rs <- scEqsRewriteRules sc eqs
  basics <- basic_ss sc
  let ss = addRules rs basics
  t' <- rewriteSharedTerm sc ss t
  let (args, _) = asLambdaList t'
      argNames = map fst args
  --putStrLn "Simulating..."
  (labels, lit) <- SBVSim.sbvSolve sc t'
  --putStrLn "Checking..."
  m <- satWith conf lit
  -- print m
  if modelExists m
    then do
      -- putStrLn "SAT"
      tt <- scApplyPreludeTrue sc
      return (getLabels labels m (SBV.getModelDictionary m) argNames, g {goalTerm = tt})
    else do
      -- putStrLn "UNSAT"
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = ft })

getLabels :: [SBVSim.Labeler] -> SBV.SatResult -> Map.Map String CW -> [String] -> SV.SatResult
getLabels ls m d argNames =
  case fmap getLabel ls of
    [x] -> SV.Sat x
    xs -> SV.SatMulti (zip argNames xs)
  where
    getLabel :: SBVSim.Labeler -> FiniteValue
    getLabel (SBVSim.BoolLabel s) = FVBit . fromJust $ SBV.getModelValue s m
    getLabel (SBVSim.WordLabel s) = d Map.! s &
      (\(KBounded _ n)-> FVWord (fromIntegral n)) . SBV.cwKind <*> (\(CWInteger i)-> i) . SBV.cwVal
    getLabel (SBVSim.VecLabel xs) = FVVec t $ map getLabel (V.toList xs)
      where t = error "FIXME getLabel VecLabel"
    getLabel (SBVSim.TupleLabel xs) = FVTuple $ map getLabel (V.toList xs)
    getLabel (SBVSim.RecLabel xs) = FVRec $ fmap getLabel xs

satBoolector :: SharedContext s -> ProofScript s SV.SatResult
satBoolector = satSBV Boolector.sbvCurrentSolver

satZ3 :: SharedContext s -> ProofScript s SV.SatResult
satZ3 = satSBV Z3.sbvCurrentSolver

satCVC4 :: SharedContext s -> ProofScript s SV.SatResult
satCVC4 = satSBV CVC4.sbvCurrentSolver

satMathSAT :: SharedContext s -> ProofScript s SV.SatResult
satMathSAT = satSBV MathSAT.sbvCurrentSolver

satYices :: SharedContext s -> ProofScript s SV.SatResult
satYices = satSBV Yices.sbvCurrentSolver

satWithExporter :: (SharedContext s -> FilePath -> SharedTerm s -> IO ())
                -> SharedContext s
                -> String
                -> String
                -> ProofScript s SV.SatResult
satWithExporter exporter sc path ext = StateT $ \g -> do
  exporter sc ((path ++ goalName g) ++ ext) (goalTerm g)
  unsatResult sc g

satAIG :: SharedContext s -> FilePath -> ProofScript s SV.SatResult
satAIG sc path = satWithExporter writeAIG sc path ".aig"

satCNF :: SharedContext s -> FilePath -> ProofScript s SV.SatResult
satCNF sc path = satWithExporter writeCNF sc path ".cnf"

satExtCore :: SharedContext s -> FilePath -> ProofScript s SV.SatResult
satExtCore sc path = satWithExporter (const writeCore) sc path ".extcore"

satSMTLib1 :: SharedContext s -> FilePath -> ProofScript s SV.SatResult
satSMTLib1 sc path = satWithExporter writeSMTLib1 sc path ".smt"

satSMTLib2 :: SharedContext s -> FilePath -> ProofScript s SV.SatResult
satSMTLib2 sc path = satWithExporter writeSMTLib2 sc path ".smt2"

liftCexBB :: [FiniteType] -> [Bool] -> Either String [FiniteValue]
liftCexBB shapes bs =
  case Old.liftCounterExamples shapes bs of
    Left err -> Left err
    Right bvals -> Right (map convertOldBValue bvals)

-- | FIXME: temporary
convertOldBValue :: Old.BValue Bool -> FiniteValue
convertOldBValue bval =
  case bval of
    Old.BBool b    -> FVBit b
    -- | FIXME: this fails for vectors of length 0
    Old.BVector vv -> FVVec t (map convertOldBValue (V.toList vv))
      where t = Old.getShape (V.head vv)
    Old.BTuple vs  -> FVTuple (map convertOldBValue vs)
    Old.BRecord vm -> FVRec (fmap convertOldBValue vm)

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
provePrim :: SharedContext s -> ProofScript s SV.SatResult
          -> SharedTerm s -> IO SV.ProofResult
provePrim sc script t = do
  t' <- scNegate sc t
  (r, _) <- runStateT script (ProofGoal "prove" t')
  return (SV.flipSatResult r)

provePrintPrim :: SharedContext s -> ProofScript s SV.SatResult
               -> SharedTerm s -> IO (Theorem s)
provePrintPrim sc script t = do
  t' <- scNegate sc t
  (r, _) <- runStateT script (ProofGoal "prove" t')
  case r of
    SV.Unsat -> putStrLn "Valid" >> return (Theorem t)
    _ -> fail (show (SV.flipSatResult r))

satPrim :: SharedContext s -> ProofScript s SV.SatResult -> SharedTerm s
        -> IO SV.SatResult
satPrim _sc script t = do
  (r, _) <- runStateT script (ProofGoal "sat" t)
  return r

satPrintPrim :: SharedContext s -> ProofScript s SV.SatResult
             -> SharedTerm s -> IO ()
satPrintPrim _sc script t = do
  (r, _) <- runStateT script (ProofGoal "sat" t)
  print r

rewritePrim :: SharedContext s -> Simpset (SharedTerm s) -> SharedTerm s -> IO (SharedTerm s)
rewritePrim sc ss t = rewriteSharedTerm sc ss t

addsimp :: SharedContext s -> Theorem s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp _sc (Theorem t) ss = addRule (ruleOfProp t) ss

addsimp' :: SharedContext s -> SharedTerm s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp' _sc t ss = addRule (ruleOfProp t) ss

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

check_term :: SharedContext s -> SharedTerm s -> IO ()
check_term sc t = scTypeCheck sc t >>= print

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

extIdx :: SharedTerm s -> Maybe VarIndex
extIdx (STApp _ (FTermF (ExtCns ec))) = Just (ecVarIndex ec)
extIdx _ = Nothing

extName :: SharedTerm s -> Maybe String
extName (STApp _ (FTermF (ExtCns ec))) = Just (ecName ec)
extName _ = Nothing

bindAllExts :: SharedContext s
            -> SharedTerm s
            -> IO (SharedTerm s)
bindAllExts sc body = bindExts sc (getAllExts body) body

-- | Return a list of all ExtCns subterms in the given term, sorted by
-- index.
getAllExts :: SharedTerm s -> [SharedTerm s]
getAllExts t@(STApp _ tf) = sortBy (comparing extIdx) $ Set.toList args
    where (seen, exts) = getExtCns (Set.empty, Set.empty) t
          args = snd $ foldl' getExtCns (seen, exts) tf
          getExtCns (is, a) (STApp idx _) | Set.member idx is = (is, a)
          getExtCns (is, a) t'@(STApp idx (FTermF (ExtCns _))) =
            (Set.insert idx is, Set.insert t' a)
          getExtCns (is, a) (STApp idx tf') =
            foldl' getExtCns (Set.insert idx is, a) tf'

-- | Apply the given SharedTerm to the given values, and evaluate to a
-- final value.
cexEvalFn :: SharedContext s -> [FiniteValue] -> SharedTerm s
          -> IO Value
cexEvalFn sc args tm = do
  -- NB: there may be more args than exts, and this is ok. One side of
  -- an equality may have more free variables than the other,
  -- particularly in the case where there is a counter-example.
  let exts = getAllExts tm
  args' <- mapM (scFiniteValue sc) args
  let is = mapMaybe extIdx exts
      argMap = Map.fromList (zip is args')
      eval = evalGlobal (scModule sc) preludePrims
  tm' <- scInstantiateExt sc argMap tm
  --ty <- scTypeCheck sc tm'
  --putStrLn $ "Type of cex eval term: " ++ show ty
  return $ evalSharedTerm eval tm'

toValueCase :: (SV.FromValue s b) =>
               SharedContext s
            -> (SharedContext s -> b -> SV.Value s -> SV.Value s -> IO (SV.Value s))
            -> SV.Value s
toValueCase sc prim =
  SV.VLambda $ \b -> return $
  SV.VLambda $ \v1 -> return $
  SV.VLambda $ \v2 ->
  prim sc (SV.fromValue b) v1 v2

caseProofResultPrim :: SharedContext s -> SV.ProofResult
                    -> SV.Value s -> SV.Value s
                    -> IO (SV.Value s)
caseProofResultPrim sc pr vValid vInvalid = do
  case pr of
    SV.Valid -> return vValid
    SV.Invalid v -> do t <- SV.mkTypedTerm sc =<< scFiniteValue sc v
                       SV.applyValue sc vInvalid (SV.toValue t)
    SV.InvalidMulti _ -> fail $ "multi-value counter-example"

caseSatResultPrim :: SharedContext s -> SV.SatResult
                  -> SV.Value s -> SV.Value s
                  -> IO (SV.Value s)
caseSatResultPrim sc sr vUnsat vSat = do
  case sr of
    SV.Unsat -> return vUnsat
    SV.Sat v -> do t <- SV.mkTypedTerm sc =<< scFiniteValue sc v
                   SV.applyValue sc vSat (SV.toValue t)
    SV.SatMulti _ -> fail $ "multi-value satisfying assignment"
