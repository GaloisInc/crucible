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
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
-- import Data.Either (partitionEithers)
import Data.Foldable (foldl')
import Data.List (isPrefixOf, sortBy)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import qualified Data.Vector as V
import System.Directory
import System.IO
import System.Process
-- import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read


import qualified Verifier.Java.Codebase as JSS
-- import Verifier.Java.SAWBackend (javaModule)
-- import Verifier.LLVM.Backend.SAW (llvmModule)

import Verifier.SAW.Constant
import Verifier.SAW.ExternalFormat
import Verifier.SAW.FiniteValue ( FiniteType(..), FiniteValue(..)
                                , scFiniteValue, fvVec, readFiniteValues
                                , finiteTypeOf
                                )
import Verifier.SAW.Evaluator hiding (applyAll)
import Verifier.SAW.Prelude
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.TypedAST hiding (instantiateVarList)

import qualified SAWScript.SBVParser as SBV
import SAWScript.ImportAIG

import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import qualified SAWScript.Value as SV

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.Simulator.SBV as SBVSim

import qualified Data.ABC as ABC
import qualified Data.SBV as SBV
import Data.SBV.Internals

import Data.ABC (giaNetwork)
import qualified Data.ABC.GIA as GIA
import qualified Data.AIG as AIG

import qualified Cryptol.TypeCheck.AST as C
import Cryptol.Utils.PP (pretty)

import qualified Data.SBV.Bridge.Boolector as Boolector
import qualified Data.SBV.Bridge.Z3 as Z3
import qualified Data.SBV.Bridge.CVC4 as CVC4
import qualified Data.SBV.Bridge.Yices as Yices
import qualified Data.SBV.Bridge.MathSAT as MathSAT
import Data.SBV (satWith, SMTConfig, Predicate, compileToSMTLib)

data BuiltinContext = BuiltinContext { biSharedContext :: SharedContext SAWCtx
                                     , biJavaCodebase  :: JSS.Codebase
                                     }

--topReturn :: (a :: sort 0) -> a -> TopLevel a;
topReturn :: () -> Value -> SC s Value
topReturn _ = return

--topBind :: (a b :: sort 0) -> TopLevel a -> (a -> TopLevel b) -> TopLevel b;
topBind :: () -> () -> SC s Value -> (Value -> SC s Value) -> SC s Value
topBind _ _ = (>>=)

definePrim :: SharedContext s -> String -> TypedTerm s -> IO (TypedTerm s)
definePrim sc name (TypedTerm schema rhs) = TypedTerm schema <$> scConstant sc ident rhs
  where ident = mkIdent (moduleName (scModule sc)) name

sbvUninterpreted :: SharedContext s -> String -> SharedTerm s -> IO (Uninterp s)
sbvUninterpreted _ s t = return $ Uninterp (s, t)

readBytes :: SharedContext SAWCtx -> FilePath -> IO (TypedTerm SAWCtx)
readBytes sc path = do
  content <- BS.readFile path
  let len = BS.length content
  let bytes = BS.unpack content
  e <- scBitvector sc 8
  xs <- mapM (scBvConst sc 8 . toInteger) bytes
  trm <- scVector sc e xs
  let schema = C.Forall [] [] (C.tSeq (C.tNum len) (C.tSeq (C.tNum (8::Int)) C.tBit))
  return (TypedTerm schema trm)

readSBV :: BuiltinContext -> Options -> FilePath -> [Uninterp SAWCtx] -> IO (TypedTerm SAWCtx)
readSBV bic opts path unintlst =
    do let sc = biSharedContext bic
       pgm <- SBV.loadSBV path
       let schema = C.Forall [] [] (toCType (SBV.typOf pgm))
       trm <- SBV.parseSBVPgm sc (\s _ -> Map.lookup s unintmap) pgm
       when (extraChecks opts) $ do
         tcr <- scTypeCheck sc trm
         case tcr of
           Left err ->
             putStr $ unlines $
             ("Type error reading " ++ path ++ ":") : prettyTCError err
           Right _ -> return () -- TODO: check that it matches 'schema'?
       return (TypedTerm schema trm)
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
readAIGPrim :: SharedContext s -> FilePath -> IO (TypedTerm s)
readAIGPrim sc f = do
  exists <- doesFileExist f
  unless exists $ fail $ "AIG file " ++ f ++ " not found."
  et <- readAIG sc f
  case et of
    Left err -> fail $ "Reading AIG failed: " ++ err
    Right t -> mkTypedTerm sc t

{-
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
-}

-- | Write a @SharedTerm@ representing a theorem or an arbitrary
-- function to an AIG file.
writeAIG :: SharedContext s -> FilePath -> TypedTerm s -> IO ()
writeAIG sc f t = withBE $ \be -> do
  ls <- BBSim.bitBlastTerm be sc (ttTerm t)
  ABC.writeAiger f (ABC.Network be (ABC.bvToList ls))
  return ()

writeCNF :: SharedContext s -> FilePath -> TypedTerm s -> IO ()
writeCNF sc f t = withBE $ \be -> do
  ls <- BBSim.bitBlastTerm be sc (ttTerm t)
  case AIG.bvToList ls of
    [l] -> do
      _ <- GIA.writeCNF be l f
      return ()
    _ -> fail "writeCNF: non-boolean term"

-- | Write a @SharedTerm@ representing a theorem to an SMT-Lib version
-- 1 file.
writeSMTLib1 :: SharedContext s -> FilePath -> TypedTerm s -> IO ()
writeSMTLib1 sc f t = do
  (_, _, l) <- prepSBV sc t
  txt <- compileToSMTLib False True l
  writeFile f txt

-- | Write a @SharedTerm@ representing a theorem to an SMT-Lib version
-- 2 file.
writeSMTLib2 :: SharedContext s -> FilePath -> TypedTerm s -> IO ()
writeSMTLib2 sc f t = do
  (_, _, l) <- prepSBV sc t
  txt <- compileToSMTLib True True l
  writeFile f txt

writeCore :: FilePath -> TypedTerm s -> IO ()
writeCore path t = writeFile path (scWriteExternal (ttTerm t))

readCore :: SharedContext s -> FilePath -> IO (TypedTerm s)
readCore sc path = mkTypedTerm sc =<< scReadExternal sc =<< readFile path

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
  putStrLn (scPrettyTerm (ttTerm (goalTerm goal)))
  return ((), goal)

unfoldGoal :: SharedContext s -> [String] -> ProofScript s ()
unfoldGoal sc names = StateT $ \goal -> do
  let ids = map (mkIdent (moduleName (scModule sc))) names
  let TypedTerm schema trm = goalTerm goal
  trm' <- scUnfoldConstants sc ids trm
  return ((), goal { goalTerm = TypedTerm schema trm' })

simplifyGoal :: SharedContext s -> Simpset (SharedTerm s) -> ProofScript s ()
simplifyGoal sc ss = StateT $ \goal -> do
  let TypedTerm schema trm = goalTerm goal
  trm' <- rewriteSharedTerm sc ss trm
  return ((), goal { goalTerm = TypedTerm schema trm' })

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
{-
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
-}

returnsBool :: SharedTerm s -> Bool
returnsBool ((asBoolType . snd . asPiList) -> Just ()) = True
returnsBool _ = False

checkBoolean :: SharedContext s -> SharedTerm s -> IO ()
checkBoolean sc t = do
  ty <- scTypeCheckError sc t
  unless (returnsBool ty) $
    fail $ "Attempting to prove a term that returns a non-boolean type: " ++
           show ty

checkBooleanType :: C.Type -> IO ()
checkBooleanType (C.tIsBit -> True) = return ()
checkBooleanType (C.tIsFun -> Just (_, ty')) = checkBooleanType ty'
checkBooleanType ty =
  fail $ "Attempting to prove a term that returns a non-boolean type: " ++ pretty ty

checkBooleanSchema :: C.Schema -> IO ()
checkBooleanSchema (C.Forall [] [] t) = checkBooleanType t
checkBooleanSchema s =
  fail $ "Attempting to prove a term with polymorphic type: " ++ pretty s

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC.
satABC :: SharedContext s -> ProofScript s SV.SatResult
satABC sc = StateT $ \g -> AIG.withNewGraph giaNetwork $ \be -> do
  let TypedTerm schema t = goalTerm g
  checkBooleanSchema schema
  let (args, _) = asLambdaList t
      argNames = map fst args
  -- putStrLn "Simulating..."
  (shapes, lit0) <- BBSim.bitBlast be sc t
  let lit = case goalQuant g of
        Existential -> lit0
        Universal -> AIG.not lit0
  -- putStrLn "Checking..."
  satRes <- AIG.checkSat be lit
  case satRes of
    AIG.Unsat -> do
      -- putStrLn "UNSAT"
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = TypedTerm schema ft })
    AIG.Sat cex -> do
      -- putStrLn "SAT"
      let r = liftCexBB shapes cex
      tt <- scApplyPreludeTrue sc
      case r of
        Left err -> fail $ "Can't parse counterexample: " ++ err
        Right [v] ->
          return (SV.Sat v, g { goalTerm = TypedTerm schema tt })
        Right vs -> do
          return (SV.SatMulti (zip argNames vs), g { goalTerm = TypedTerm schema tt })
    AIG.SatUnknown -> fail "Unknown result from ABC"

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

satExternal :: Bool -> SharedContext s -> String -> [String]
            -> ProofScript s SV.SatResult
satExternal doCNF sc execName args = StateT $ \g -> withBE $ \be -> do
  let cnfName = goalName g ++ ".cnf"
      TypedTerm schema t = goalTerm g
      argNames = map fst (fst (asLambdaList t))
  checkBoolean sc t
  (path, fh) <- openTempFile "." cnfName
  hClose fh -- Yuck. TODO: allow writeCNF et al. to work on handles.
  let args' = map replaceFileName args
      replaceFileName "%f" = path
      replaceFileName a = a
  (shapes, l0) <- BBSim.bitBlast be sc t
  let l = case goalQuant g of
        Existential -> l0
        Universal -> AIG.not l0
  vars <- (if doCNF then GIA.writeCNF else writeAIGWithMapping) be l path
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
          return (SV.Sat v, g { goalTerm = TypedTerm schema tt })
        Right vs -> do
          return (SV.SatMulti (zip argNames vs), g { goalTerm = TypedTerm schema tt })
    (["s UNSATISFIABLE"], []) -> do
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = TypedTerm schema ft })
    _ -> fail $ "Unexpected result from SAT solver:\n" ++ out

writeAIGWithMapping :: GIA.GIA s -> GIA.Lit s -> FilePath -> IO [Int]
writeAIGWithMapping be l path = do
  nins <- GIA.inputCount be
  ABC.writeAiger path (ABC.Network be [l])
  return [1..nins]

unsatResult :: SharedContext s -> ProofGoal s
            -> IO (SV.SatResult, ProofGoal s)
unsatResult sc g = do
  let schema = C.Forall [] [] C.tBit
  ft <- scApplyPreludeFalse sc
  return (SV.Unsat, g { goalTerm = TypedTerm schema ft })

rewriteEqs :: SharedContext s -> TypedTerm s -> IO (TypedTerm s)
rewriteEqs sc (TypedTerm schema t) = do
  let eqs = map (mkIdent preludeName)
            [ "eq_Fin", "eq_Bool", "eq_Nat", "eq_bitvector", "eq_VecBool"
            , "eq_VecVec" ]
  rs <- scEqsRewriteRules sc eqs
  ss <- addRules rs <$> basic_ss sc
  t' <- rewriteSharedTerm sc ss t
  return (TypedTerm schema t')

prepSBV :: SharedContext s -> TypedTerm s
        -> IO (SharedTerm s, [SBVSim.Labeler], Predicate)
prepSBV sc tt = do
  TypedTerm schema t' <- rewriteEqs sc tt
  checkBooleanSchema schema
  (labels, lit) <- SBVSim.sbvSolve sc t'
  return (t', labels, lit)

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using SBV. (Currently ignores satisfying assignments.)
satSBV :: SMTConfig -> SharedContext s -> ProofScript s SV.SatResult
satSBV conf sc = StateT $ \g -> do
  (t', labels, lit0) <- prepSBV sc (goalTerm g)
  let lit = case goalQuant g of
        Existential -> lit0
        Universal -> liftM SBV.bnot lit0
  let (args, _) = asLambdaList t'
      argNames = map fst args
  SBV.SatResult r <- satWith conf lit
  case r of
    SBV.Satisfiable {} -> do
      let schema = C.Forall [] [] C.tBit
      tt <- scApplyPreludeTrue sc
      return (getLabels labels r (SBV.getModelDictionary r) argNames, g {goalTerm = TypedTerm schema tt})
    SBV.Unsatisfiable {} -> do
      let schema = C.Forall [] [] C.tBit
      ft <- scApplyPreludeFalse sc
      return (SV.Unsat, g { goalTerm = TypedTerm schema ft })
    SBV.Unknown {} -> fail "Prover returned Unknown"
    SBV.ProofError _ ls -> fail . unlines $ "Prover returned error: " : ls
    SBV.TimeOut {} -> fail "Prover timed out"

getLabels :: [SBVSim.Labeler] -> SBV.SMTResult -> Map.Map String CW -> [String] -> SV.SatResult
getLabels ls m d argNames =
  case fmap getLabel ls of
    [x] -> SV.Sat x
    xs -> SV.SatMulti (zip argNames xs)
  where
    getLabel :: SBVSim.Labeler -> FiniteValue
    getLabel (SBVSim.BoolLabel s) = FVBit . fromJust $ SBV.getModelValue s m
    getLabel (SBVSim.WordLabel s) = d Map.! s &
      (\(KBounded _ n)-> FVWord (fromIntegral n)) . SBV.cwKind <*> (\(CWInteger i)-> i) . SBV.cwVal
    getLabel (SBVSim.VecLabel xs)
      | V.null xs = error "getLabel of empty vector"
      | otherwise = fvVec t vs
      where vs = map getLabel (V.toList xs)
            t = finiteTypeOf (head vs)
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

satWithExporter :: (SharedContext s -> FilePath -> TypedTerm s -> IO ())
                -> SharedContext s
                -> String
                -> String
                -> ProofScript s SV.SatResult
satWithExporter exporter sc path ext = StateT $ \g -> do
  when (goalQuant g == Universal)
    (fail "satWithExporter: Universal quantification unimplemented")
  let t = goalTerm g
  checkBooleanSchema (ttSchema t)
  exporter sc ((path ++ goalName g) ++ ext) t
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
liftCexBB tys bs =
  case readFiniteValues tys bs of
    Nothing -> Left "Failed to lift counterexample"
    Just fvs -> Right fvs

-- | Translate a @SharedTerm@ representing a theorem for input to the
-- given validity-checking script and attempt to prove it.
provePrim :: SharedContext s -> ProofScript s SV.SatResult
          -> TypedTerm s -> IO SV.ProofResult
provePrim _sc script t = do
  checkBooleanSchema (ttSchema t)
  r <- evalStateT script (ProofGoal Universal "prove" t)
  return (SV.flipSatResult r)

provePrintPrim :: SharedContext s -> ProofScript s SV.SatResult
               -> TypedTerm s -> IO (Theorem s)
provePrintPrim _sc script t = do
  checkBooleanSchema (ttSchema t)
  r <- evalStateT script (ProofGoal Universal "prove" t)
  case r of
    SV.Unsat -> putStrLn "Valid" >> return (Theorem t)
    _ -> fail (show (SV.flipSatResult r))

satPrim :: SharedContext s -> ProofScript s SV.SatResult -> TypedTerm s
        -> IO SV.SatResult
satPrim _sc script t = do
  checkBooleanSchema (ttSchema t)
  evalStateT script (ProofGoal Existential "sat" t)

satPrintPrim :: SharedContext s -> ProofScript s SV.SatResult
             -> TypedTerm s -> IO ()
satPrintPrim _sc script t = do
  r <- evalStateT script (ProofGoal Existential "sat" t)
  print r

cryptolSimpset :: SharedContext s -> IO (Simpset (SharedTerm s))
cryptolSimpset sc = scSimpset sc cryptolDefs [] []
  where cryptolDefs = moduleDefs CryptolSAW.cryptolModule

addPreludeEqs :: SharedContext s -> [String] -> Simpset (SharedTerm s)
              -> IO (Simpset (SharedTerm s))
addPreludeEqs sc names ss = do
  eqRules <- mapM (scEqRewriteRule sc) (map qualify names)
  return (addRules eqRules ss)
    where qualify = mkIdent (mkModuleName ["Prelude"])

rewritePrim :: SharedContext s -> Simpset (SharedTerm s) -> TypedTerm s -> IO (TypedTerm s)
rewritePrim sc ss (TypedTerm schema t) = do
  t' <- rewriteSharedTerm sc ss t
  return (TypedTerm schema t')

addsimp :: SharedContext s -> Theorem s -> Simpset (SharedTerm s) -> Simpset (SharedTerm s)
addsimp _sc (Theorem t) ss = addRule (ruleOfProp (ttTerm t)) ss

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
check_term sc t = scTypeCheckError sc t >>= print

checkTypedTerm :: SharedContext s -> TypedTerm s -> IO ()
checkTypedTerm sc (TypedTerm _schema t) = scTypeCheckError sc t >>= print

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
extIdx (unwrapTermF -> FTermF (ExtCns ec)) = Just (ecVarIndex ec)
extIdx _ = Nothing

extName :: SharedTerm s -> Maybe String
extName (unwrapTermF -> FTermF (ExtCns ec)) = Just (ecName ec)
extName _ = Nothing

freshBitvectorPrim :: SharedContext s -> String -> Int -> IO (TypedTerm s)
freshBitvectorPrim sc x n = do
  ty <- scBitvector sc (fromIntegral n)
  tm <- scFreshGlobal sc x ty
  mkTypedTerm sc tm

abstractSymbolicPrim :: SharedContext s -> TypedTerm s -> IO (TypedTerm s)
abstractSymbolicPrim sc (TypedTerm _ t) =
  mkTypedTerm sc =<< bindAllExts sc t

bindAllExts :: SharedContext s
            -> SharedTerm s
            -> IO (SharedTerm s)
bindAllExts sc body = bindExts sc (getAllExts body) body

-- | Return a list of all ExtCns subterms in the given term, sorted by
-- index.
getAllExts :: SharedTerm s -> [SharedTerm s]
getAllExts t = sortBy (comparing extIdx) $ Set.toList args
    where (seen, exts) = getExtCns (Set.empty, Set.empty) t
          tf = unwrapTermF t
          args = snd $ foldl' getExtCns (seen, exts) tf
          getExtCns (is, a) (STApp idx _) | Set.member idx is = (is, a)
          getExtCns (is, a) t'@(STApp idx (FTermF (ExtCns _))) =
            (Set.insert idx is, Set.insert t' a)
          getExtCns (is, a) t'@(Unshared (FTermF (ExtCns _))) =
            (is, Set.insert t' a)
          getExtCns (is, a) (STApp idx tf') =
            foldl' getExtCns (Set.insert idx is, a) tf'
          getExtCns (is, a) (Unshared tf') =
            foldl' getExtCns (is, a) tf'

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
  return $ evalSharedTerm eval tm'

toValueCase :: (SV.FromValue b) =>
               SharedContext SAWCtx
            -> (SharedContext SAWCtx -> b -> SV.Value -> SV.Value -> IO SV.Value)
            -> SV.Value
toValueCase sc prim =
  SV.VLambda $ \b -> return $
  SV.VLambda $ \v1 -> return $
  SV.VLambda $ \v2 ->
  prim sc (SV.fromValue b) v1 v2

caseProofResultPrim :: SharedContext SAWCtx -> SV.ProofResult
                    -> SV.Value -> SV.Value
                    -> IO SV.Value
caseProofResultPrim sc pr vValid vInvalid = do
  case pr of
    SV.Valid -> return vValid
    SV.Invalid v -> do t <- mkTypedTerm sc =<< scFiniteValue sc v
                       SV.applyValue vInvalid (SV.toValue t)
    SV.InvalidMulti _ -> fail $ "multi-value counter-example"

caseSatResultPrim :: SharedContext SAWCtx -> SV.SatResult
                  -> SV.Value -> SV.Value
                  -> IO SV.Value
caseSatResultPrim sc sr vUnsat vSat = do
  case sr of
    SV.Unsat -> return vUnsat
    SV.Sat v -> do t <- mkTypedTerm sc =<< scFiniteValue sc v
                   SV.applyValue vSat (SV.toValue t)
    SV.SatMulti _ -> fail $ "multi-value satisfying assignment"
