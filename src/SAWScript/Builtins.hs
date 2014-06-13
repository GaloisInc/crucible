{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.Builtins where

import Control.Applicative
import Control.Lens
import Control.Monad.Error
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.Leijen hiding ((<$>))

import qualified Verinf.Symbolic.Lit.ABC_GIA as GIA

import qualified Verifier.Java.Codebase as JSS
import Verifier.Java.SAWBackend (javaModule)
import qualified Verifier.LLVM.Codebase as LSS

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

import SAWScript.Proof
import SAWScript.Utils

import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verinf.Symbolic as BE

import Data.ABC (aigNetwork)
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
  let eqs = map (mkIdent preludeName) [ "eq_Bool" ]
      defs = map (mkIdent preludeName) [ "get_single" ]
             ++
             map (mkIdent (moduleName javaModule))
                 [ "ecJoin", "ecSplit", "ecExtend", "longExtend" ]
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

-- | Bit-blast a @SharedTerm@ representing a theorem and check its
-- satisfiability using ABC. (Currently ignores satisfying assignments.)
satABC' :: SharedContext s -> ProofScript s ProofResult
satABC' sc = StateT $ \t -> AIG.withNewGraph aigNetwork $ \be -> do
  putStrLn "Simulating..."
  lit <- BBSim.bitBlast be sc t
  putStrLn "Checking..."
  satRes <- AIG.checkSat be lit
  case satRes of
    AIG.Unsat -> do putStrLn "UNSAT"
                    (,) () <$> scApplyPreludeFalse sc
    AIG.Sat _ -> do putStrLn "SAT"
                    (,) () <$> scApplyPreludeTrue sc
    _ -> fail "ABC returned Unknown for SAT query."

satAIG :: SharedContext s -> FilePath -> ProofScript s ProofResult
satAIG sc path = StateT $ \t -> do
  writeAIG sc path t
  (,) () <$> scApplyPreludeFalse sc

satExtCore :: SharedContext s -> FilePath -> ProofScript s ProofResult
satExtCore sc path = StateT $ \t -> do
  writeCore path t
  (,) () <$> scApplyPreludeFalse sc

satSMTLib1 :: SharedContext s -> FilePath -> ProofScript s ProofResult
satSMTLib1 sc path = StateT $ \t -> do
  writeSMTLib1 sc path t
  (,) () <$> scApplyPreludeFalse sc

satSMTLib2 :: SharedContext s -> FilePath -> ProofScript s ProofResult
satSMTLib2 sc path = StateT $ \t -> do
  writeSMTLib2 sc path t
  (,) () <$> scApplyPreludeFalse sc

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
