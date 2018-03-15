-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.SAWCoreBackend
-- Description      : Crucible interface for generating SAWCore
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides a Crucible backend that produces SAWCore terms.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.Solver.SAWCoreBackend where

import           Control.Exception ( assert, throw )
import           Control.Lens
import           Control.Monad
import           Data.IORef
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Word(Word64)
import qualified Data.Text as Text

import qualified Data.ABC.GIA as GIA
import qualified Data.AIG as AIG
import           Numeric.Natural

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Config
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.SatResult
import qualified Lang.Crucible.Solver.SimpleBuilder as SB
import           Lang.Crucible.Solver.Symbol
import qualified Lang.Crucible.Solver.WeightedSum as WSum

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.TypedAST as SC

data SAWCruciblePersonality sym = SAWCruciblePersonality

-- | The SAWCoreBackend is a crucible backend that represents symbolic values
--   as SAWCore terms.
data SAWCoreState n
  = SAWCoreState
    { saw_ctx       :: SC.SharedContext                         -- ^ the main SAWCore datastructure for building shared terms
    , saw_inputs    :: IORef (Seq (SC.ExtCns SC.Term ))
      -- ^ a record of all the symbolic input variables created so far,
      --   in the order they were created

    , saw_symMap :: !(Map Word64 (SC.SharedContext -> [SC.Term] -> IO SC.Term))
      -- ^ What to do with uninterpred functions.
      -- The key is the "indexValue" of the "symFunId" for the function

    , saw_elt_cache :: SB.IdxCache n SAWElt
    , saw_assertions  :: Seq (Assertion (Pred (SAWCoreBackend n)))
    , saw_obligations :: Seq (Seq (Pred (SAWCoreBackend n)), Assertion (Pred (SAWCoreBackend n)))
    , saw_config    :: SimConfig SAWCruciblePersonality (SAWCoreBackend n)
    }

sawCheckPathSat :: ConfigOption Bool
sawCheckPathSat = configOption "saw.check_path_sat"

sawOptions :: Monad m => [ConfigDesc m]
sawOptions =
  [ opt sawCheckPathSat False
    "Check the satisfiability of path conditions on branches"
  ]

data SAWElt (bt :: BaseType) where
  SAWElt :: !SC.Term -> SAWElt bt

  -- This is a term that represents an integer, but has an
  -- implicit integer-to-real conversion.
  IntToRealSAWElt :: !(SAWElt BaseIntegerType) -> SAWElt BaseRealType
  -- This is a SAWCore term that represents a natural number, but has an
  -- implicit nat-to-integer conversion.
  NatToIntSAWElt :: !(SAWElt BaseNatType) -> SAWElt BaseIntegerType

type SAWCoreBackend n = SB.SimpleBuilder n SAWCoreState

baseSCType :: SC.SharedContext -> BaseTypeRepr tp -> IO SC.Term
baseSCType ctx bt =
  case bt of
    BaseBoolRepr -> SC.scBoolType ctx
    BaseBVRepr w -> SC.scBitvector ctx $ fromIntegral (natValue w)
    BaseNatRepr  -> SC.scNatType ctx
    BaseIntegerRepr -> SC.scIntegerType ctx
    BaseArrayRepr indexTypes range ->
      case Ctx.viewAssign indexTypes of
        Ctx.AssignExtend b dom -> do
          when (not (Ctx.null b)) $ do
            fail $ "SAW backend only supports single element arrays."
          join $ SC.scFun ctx <$> baseSCType ctx dom
                              <*> baseSCType ctx range
    BaseComplexRepr  -> fail "SAW backend does not support complex values: baseSCType"
    BaseRealRepr     -> fail "SAW backend does not support real values: baseSCType"
    BaseStructRepr _ -> fail "FIXME baseSCType for structures"

-- | Create a new symbolic variable.
sawCreateVar :: SAWCoreBackend n
             -> String                                       -- ^ the name of the variable
             -> SC.Term
             -> IO SC.Term
sawCreateVar sym nm tp = do
  st <- readIORef (SB.sbStateManager sym)
  let sc = saw_ctx st
  i <- SC.scFreshGlobalVar sc
  let ec = SC.EC i ("var_"++nm++"_"++show i) tp
  t <- SC.scFlatTermF sc (SC.ExtCns ec)
  modifyIORef (saw_inputs st) (\xs -> xs Seq.|> ec)
  return t

bindSAWTerm :: SAWCoreBackend n
            -> BaseTypeRepr bt
            -> SC.Term
            -> IO (SB.Elt n bt)
bindSAWTerm sym bt t = do
  st <- readIORef $ SB.sbStateManager sym
  sbVar@(SB.BoundVarElt bv) <- freshConstant sym emptySymbol bt
  SB.insertIdxValue (saw_elt_cache st) (SB.bvarId bv) (SAWElt t)
  return sbVar

newSAWCoreBackend ::
  SC.SharedContext ->
  NonceGenerator IO s ->
  SimConfig SAWCruciblePersonality (SAWCoreBackend s) ->
  IO (SAWCoreBackend s)
newSAWCoreBackend sc gen cfg = do
  inpr <- newIORef Seq.empty
  ch   <- SB.newIdxCache
  let st = SAWCoreState
              { saw_ctx = sc
              , saw_inputs = inpr
              , saw_symMap = Map.empty
              , saw_elt_cache = ch
              , saw_assertions = Seq.empty
              , saw_obligations = Seq.empty
              , saw_config = cfg
              }
  SB.newSimpleBuilder st gen

-- | Register an interpretation for a symbolic function.
-- This is not used during simulation, but rather, when we translate
-- crucible values back into SAW.
sawRegisterSymFunInterp ::
  SAWCoreBackend n ->
  SB.SimpleSymFn n args ret ->
  (SC.SharedContext -> [SC.Term] -> IO SC.Term) ->
  IO ()
sawRegisterSymFunInterp sym f i =
  modifyIORef (SB.sbStateManager sym) $ \s ->
      s { saw_symMap = Map.insert (indexValue (SB.symFnId f)) i (saw_symMap s) }


sawBackendSharedContext :: SAWCoreBackend n -> IO SC.SharedContext
sawBackendSharedContext sym =
  saw_ctx <$> readIORef (SB.sbStateManager sym)

-- | Run a computation with a fresh SAWCoreBackend, in the context of the
--   given module.
withSAWCoreBackend :: SC.Module -> (forall n. SAWCoreBackend n -> IO a) -> IO a
withSAWCoreBackend md f = do
  withIONonceGenerator $ \gen -> do
    cfg <- initialConfig 0 []
    sc   <- SC.mkSharedContext md
    sym  <- newSAWCoreBackend sc gen cfg
    f sym

toSC :: SAWCoreBackend n -> SB.Elt n tp -> IO SC.Term
toSC sym elt = do
     st <- readIORef $ SB.sbStateManager sym
     evaluateElt sym (saw_ctx st) (saw_elt_cache st) elt


-- | Return a shared term with type nat from a SAWElt.
scAsIntElt :: SC.SharedContext -> SAWElt BaseRealType -> IO SC.Term
scAsIntElt sc (IntToRealSAWElt (NatToIntSAWElt (SAWElt t))) = SC.scNatToInt sc t
scAsIntElt _ (IntToRealSAWElt (SAWElt t)) = return t
scAsIntElt _ SAWElt{} = fail $ "SAWbackend does not support real values."

-- | Create a Real SAWELT value from a Rational.
--
-- This fails on non-integer expressions.
scRealLit :: SC.SharedContext
          -> Rational
          -> IO (SAWElt BaseRealType)
scRealLit sc r
  | denominator r /= 1 =
    fail "SAW backend does not support real values"
  | r >= 0 =
    IntToRealSAWElt . NatToIntSAWElt . SAWElt <$> SC.scNat sc (fromInteger (numerator r))
  | otherwise =
    IntToRealSAWElt <$> scIntLit sc (numerator r)

-- | Create a SAWCore term with type 'Integer' from a Haskell Integer.
scIntLit :: SC.SharedContext -> Integer -> IO (SAWElt BaseIntegerType)
scIntLit sc i
  | i >= 0 =
    SAWElt <$> (SC.scNatToInt sc =<< SC.scNat sc (fromInteger i))
  | otherwise =
    SAWElt <$> (SC.scIntNeg sc =<< SC.scNatToInt sc =<< SC.scNat sc (fromInteger (negate i)))

-- | Create a SAWCore term with type 'Nat' from a Haskell Nat.
scNatLit :: SC.SharedContext -> Natural -> IO (SAWElt BaseNatType)
scNatLit sc n = SAWElt <$> SC.scNat sc (fromIntegral n)


scRealCmpop :: (SC.SharedContext -> SAWElt BaseIntegerType -> SAWElt BaseIntegerType -> IO (SAWElt BaseBoolType))
            -> SC.SharedContext
            -> SAWElt BaseRealType
            -> SAWElt BaseRealType
            -> IO (SAWElt BaseBoolType)
scRealCmpop intOp sc (IntToRealSAWElt x) (IntToRealSAWElt y) =
  intOp sc x y
scRealCmpop _ _ _ _ =
  fail "SAW backend does not support real values"

scRealBinop :: (SC.SharedContext -> SAWElt BaseIntegerType -> SAWElt BaseIntegerType -> IO (SAWElt BaseIntegerType))
            -> SC.SharedContext
            -> SAWElt BaseRealType
            -> SAWElt BaseRealType
            -> IO (SAWElt BaseRealType)
scRealBinop intOp sc (IntToRealSAWElt x) (IntToRealSAWElt y) =
  IntToRealSAWElt <$> intOp sc x y
scRealBinop _ _ _ _ =
  fail "SAW backend does not support real values"


scIntBinop :: (SC.SharedContext -> SAWElt BaseNatType -> SAWElt BaseNatType -> IO (SAWElt BaseNatType)) -- ^ operation on naturals
           -> (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) -- ^ operation on integers
           -> SC.SharedContext
           -> SAWElt BaseIntegerType
           -> SAWElt BaseIntegerType
           -> IO (SAWElt BaseIntegerType)
scIntBinop natOp _intOp sc (NatToIntSAWElt x) (NatToIntSAWElt y) =
  NatToIntSAWElt <$> natOp sc x y
scIntBinop _natOp intOp sc (NatToIntSAWElt (SAWElt x)) (SAWElt y) =
  SAWElt <$> join (intOp sc <$> SC.scNatToInt sc x <*> pure y)
scIntBinop _natOp intOp sc (SAWElt x) (NatToIntSAWElt (SAWElt y)) =
  SAWElt <$> join (intOp sc <$> pure x <*> SC.scNatToInt sc y)
scIntBinop _natOp intOp sc (SAWElt x) (SAWElt y) =
  SAWElt <$> intOp sc x y

scIntCmpop :: (SC.SharedContext -> SAWElt BaseNatType -> SAWElt BaseNatType -> IO (SAWElt BaseBoolType)) -- ^ operation on naturals
           -> (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) -- ^ operation on integers
           -> SC.SharedContext
           -> SAWElt BaseIntegerType
           -> SAWElt BaseIntegerType
           -> IO (SAWElt BaseBoolType)
scIntCmpop natOp _intOp sc (NatToIntSAWElt x) (NatToIntSAWElt y) =
  natOp sc x y
scIntCmpop _natOp intOp sc (NatToIntSAWElt (SAWElt x)) (SAWElt y) =
  SAWElt <$> join (intOp sc <$> SC.scNatToInt sc x <*> pure y)
scIntCmpop _natOp intOp sc (SAWElt x) (NatToIntSAWElt (SAWElt y)) =
  SAWElt <$> join (intOp sc <$> pure x <*> SC.scNatToInt sc y)
scIntCmpop _natOp intOp sc (SAWElt x) (SAWElt y) =
  SAWElt <$> intOp sc x y

scAddReal :: SC.SharedContext
          -> SAWElt BaseRealType
          -> SAWElt BaseRealType
          -> IO (SAWElt BaseRealType)
scAddReal = scRealBinop scAddInt

scAddInt :: SC.SharedContext
            -> SAWElt BaseIntegerType
            -> SAWElt BaseIntegerType
            -> IO (SAWElt BaseIntegerType)
scAddInt = scIntBinop scAddNat SC.scIntAdd

scAddNat :: SC.SharedContext
            -> SAWElt BaseNatType
            -> SAWElt BaseNatType
            -> IO (SAWElt BaseNatType)
scAddNat sc (SAWElt x) (SAWElt y) = SAWElt <$> SC.scAddNat sc x y


scMulReal :: SC.SharedContext
             -> SAWElt BaseRealType
             -> SAWElt BaseRealType
             -> IO (SAWElt BaseRealType)
scMulReal = scRealBinop scMulInt

scMulInt :: SC.SharedContext
            -> SAWElt BaseIntegerType
            -> SAWElt BaseIntegerType
            -> IO (SAWElt BaseIntegerType)
scMulInt = scIntBinop scMulNat SC.scIntMul

scMulNat :: SC.SharedContext
            -> SAWElt BaseNatType
            -> SAWElt BaseNatType
            -> IO (SAWElt BaseNatType)
scMulNat sc (SAWElt x) (SAWElt y) = SAWElt <$> SC.scMulNat sc x y

scIteReal :: SC.SharedContext
             -> SC.Term
             -> SAWElt BaseRealType
             -> SAWElt BaseRealType
             -> IO (SAWElt BaseRealType)
scIteReal sc p = scRealBinop (\sc' -> scIteInt sc' p) sc

scIteInt :: SC.SharedContext
            -> SC.Term
            -> SAWElt BaseIntegerType
            -> SAWElt BaseIntegerType
            -> IO (SAWElt BaseIntegerType)
scIteInt sc p = scIntBinop
    (\sc' -> scIteNat sc' p)
    (\sc' x y -> SC.scIntegerType sc >>= \tp -> SC.scIte sc' tp p x y)
    sc

scIteNat :: SC.SharedContext
            -> SC.Term
            -> SAWElt BaseNatType
            -> SAWElt BaseNatType
            -> IO (SAWElt BaseNatType)
scIteNat sc p (SAWElt x) (SAWElt y) =
  SAWElt <$> (SC.scNatType sc >>= \tp -> SC.scIte sc tp p x y)


scRealEq :: SC.SharedContext
         -> SAWElt BaseRealType
         -> SAWElt BaseRealType
         -> IO (SAWElt BaseBoolType)
scRealEq = scRealCmpop scIntEq

scIntEq :: SC.SharedContext
        -> SAWElt BaseIntegerType
        -> SAWElt BaseIntegerType
        -> IO (SAWElt BaseBoolType)
scIntEq = scIntCmpop scNatEq SC.scIntEq

scNatEq :: SC.SharedContext
        -> SAWElt BaseNatType
        -> SAWElt BaseNatType
        -> IO (SAWElt BaseBoolType)
scNatEq sc (SAWElt x) (SAWElt y) = SAWElt <$> SC.scEqualNat sc x y


scRealLe :: SC.SharedContext
         -> SAWElt BaseRealType
         -> SAWElt BaseRealType
         -> IO (SAWElt BaseBoolType)
scRealLe = scRealCmpop scIntLe

scIntLe :: SC.SharedContext
        -> SAWElt BaseIntegerType
        -> SAWElt BaseIntegerType
        -> IO (SAWElt BaseBoolType)
scIntLe = scIntCmpop scNatLe SC.scIntLe

scNatLe :: SC.SharedContext
        -> SAWElt BaseNatType
        -> SAWElt BaseNatType
        -> IO (SAWElt BaseBoolType)
scNatLe sc (SAWElt x) (SAWElt y) =
  do lt <- SC.scLtNat sc x y
     eq <- SC.scEqualNat sc x y
     SAWElt <$> SC.scOr sc lt eq


-- | Note: first element in the result is the right-most value in the assignment
evaluateAsgn ::
  SAWCoreBackend n ->
  SC.SharedContext ->
  SB.IdxCache n SAWElt ->
  Ctx.Assignment (SB.Elt n) args ->
  IO [SC.Term]
evaluateAsgn sym sc cache xs =
  case xs of
    Ctx.Empty -> return []
    ys Ctx.:> x ->
      do v  <- evaluateElt sym sc cache x
         vs <- evaluateAsgn sym sc cache ys
         return (v:vs)


evaluateElt :: forall n tp
             . SAWCoreBackend n
            -> SC.SharedContext
            -> SB.IdxCache n SAWElt
            -> SB.Elt n tp
            -> IO SC.Term
evaluateElt sym sc cache = f
 where
   -- Evaluate the element, and expect the result to have the same type.
   f :: SB.Elt n tp' -> IO SC.Term
   f elt = do
       st <- eval elt
       case st of
         SAWElt t -> return t
         _ -> realFail

   eval :: SB.Elt n tp' -> IO (SAWElt tp')
   eval elt = SB.idxCacheEval cache elt (go elt)

   realFail :: IO a
   realFail = fail "SAW backend does not support real values"

   go :: SB.Elt n tp' -> IO (SAWElt tp')
   go (SB.SemiRingLiteral sr x _) =
     case sr of
       SB.SemiRingNat  -> SAWElt <$> SC.scNat sc (fromIntegral x)
       SB.SemiRingInt  -> scIntLit sc x
       SB.SemiRingReal -> scRealLit sc x
   go (SB.BVElt w i _) = SAWElt <$> SC.scBvConst sc (fromIntegral (natValue w)) i

   go (SB.BoundVarElt bv) =
      case SB.bvarKind bv of
        SB.UninterpVarKind -> do
           tp <- baseSCType sc (SB.bvarType bv)
           -- SAWElt <$> sawCreateVar sym "x" tp
           SAWElt <$> sawCreateVar sym nm tp
             where nm = Text.unpack $ solverSymbolAsText $ SB.bvarName bv
        SB.LatchVarKind ->
          fail $ unwords ["SAW backend does not support latch variables"]
        SB.QuantifierVarKind ->
          fail $ unwords ["SAW backend does not support quantifier variables"]

   go (SB.NonceAppElt p) =
      case SB.nonceEltApp p of
        SB.Forall{} ->
          fail "SAW backend does not support quantifiers"
        SB.Exists{} ->
          fail "SAW backend does not support quantifiers"
        SB.ArrayFromFn{} ->
          fail "SAW backend does not support symbolic arrays"
        SB.MapOverArrays{} ->
          fail "SAW backend does not support symbolic arrays"
        SB.ArrayTrueOnEntries{} ->
          fail "SAW backend does not support symbolic arrays"
        SB.FnApp fn asgn ->
          do st <- readIORef (SB.sbStateManager sym)
             case Map.lookup (indexValue (SB.symFnId fn)) (saw_symMap st) of
               Nothing -> fail ("Unknown symbolic function: " ++ show fn)
               Just mk ->
                 do ts <- evaluateAsgn sym sc cache asgn
                    SAWElt <$> mk sc ts


   go a0@(SB.AppElt a) =
      let nyi :: Monad m => m a
          nyi = fail $ "Expression form not yet implemented in SAWCore backend:\n" ++ show a0 in
      case SB.appEltApp a of

        SB.TrueBool  -> SAWElt <$> SC.scBool sc True
        SB.FalseBool -> SAWElt <$> SC.scBool sc False
        SB.NotBool x -> SAWElt <$> (SC.scNot sc =<< f x)
        SB.AndBool x y -> SAWElt <$> join (SC.scAnd sc <$> f x <*> f y)
        SB.XorBool x y -> SAWElt <$> join (SC.scXor sc <$> f x <*> f y)
        SB.IteBool c x y ->
            SAWElt <$> join (SC.scIte sc <$> SC.scBoolType sc <*> f c <*> f x <*> f y)

        SB.SemiRingEq sr xe ye ->
          case sr of
            SB.SemiRingReal -> join (scRealEq sc <$> eval xe <*> eval ye)
            SB.SemiRingInt  -> join (scIntEq sc <$> eval xe <*> eval ye)
            SB.SemiRingNat  -> join (scNatEq sc <$> eval xe <*> eval ye)

        SB.SemiRingLe sr xe ye ->
          case sr of
            SB.SemiRingReal -> join (scRealLe sc <$> eval xe <*> eval ye)
            SB.SemiRingInt  -> join (scIntLe sc <$> eval xe <*> eval ye)
            SB.SemiRingNat  -> join (scNatLe sc <$> eval xe <*> eval ye)

        SB.SemiRingIte sr c xe ye ->
          case sr of
            SB.SemiRingReal -> join (scIteReal sc <$> f c <*> eval xe <*> eval ye)
            SB.SemiRingInt  -> join (scIteInt  sc <$> f c <*> eval xe <*> eval ye)
            SB.SemiRingNat  -> join (scIteNat  sc <$> f c <*> eval xe <*> eval ye)

        SB.SemiRingMul sr xe ye ->
           case sr of
             SB.SemiRingReal -> join (scMulReal sc <$> eval xe <*> eval ye)
             SB.SemiRingInt  -> join (scMulInt  sc <$> eval xe <*> eval ye)
             SB.SemiRingNat  -> join (scMulNat  sc <$> eval xe <*> eval ye)

        SB.SemiRingSum sr ss ->
          case sr of
            SB.SemiRingReal -> WSum.eval add smul (scRealLit sc) ss
               where add mx my = join $ scAddReal sc <$> mx <*> my
                     smul sm e = join $ scMulReal sc <$> scRealLit sc sm <*> eval e
            SB.SemiRingInt  -> WSum.eval add smul (scIntLit sc) ss
               where add mx my = join $ scAddInt sc <$> mx <*> my
                     smul sm e = join $ scMulInt sc <$> scIntLit sc sm <*> eval e
            SB.SemiRingNat  -> WSum.eval add smul (scNatLit sc) ss
               where add mx my = join $ scAddNat sc <$> mx <*> my
                     smul sm e = join $ scMulNat sc <$> scNatLit sc sm <*> eval e

        SB.RealIsInteger{} -> fail "SAW backend does not support real values"

        SB.BVTestBit i bv -> fmap SAWElt $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth bv)))
             bit <- SC.scBoolType sc
             join (SC.scAt sc w bit <$> f bv <*> SC.scNat sc (fromIntegral i))
        SB.BVEq x y -> fmap SAWElt $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth x)))
             join (SC.scBvEq sc w <$> f x <*> f y)
        SB.BVSlt x y -> fmap SAWElt $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth x)))
             join (SC.scBvSLt sc w <$> f x <*> f y)
        SB.BVUlt x y -> fmap SAWElt $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth x)))
             join (SC.scBvULt sc w <$> f x <*> f y)

        SB.ArrayEq _ _ -> fail "SAW backend does not support array equality"

        SB.RealDiv{} -> realFail
        SB.IntMod x y -> fmap SAWElt $
          join (SC.scIntMod sc <$> f x <*> f y)
        SB.RealSqrt{} -> realFail
        SB.Pi{} -> realFail
        SB.RealSin{} -> realFail
        SB.RealCos{} -> realFail
        SB.RealSinh{} -> realFail
        SB.RealCosh{} -> realFail
        SB.RealExp{} -> realFail
        SB.RealLog{} -> realFail
        SB.RealATan2{} -> realFail

        SB.BVUnaryTerm{} -> fail "SAW backend does not support the unary bitvector representation"

        SB.BVNeg _ x -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           SC.scBvNeg sc n =<< f x
        SB.BVAdd _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvAdd sc n <$> f x <*> f y)
        SB.BVMul _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvMul sc n <$> f x <*> f y)
        SB.BVUdiv _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvUDiv sc n <$> f x <*> f y)
        SB.BVUrem _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvURem sc n <$> f x <*> f y)
        SB.BVSdiv _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvSDiv sc n <$> f x <*> f y)
        SB.BVSrem _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvSRem sc n <$> f x <*> f y)
        SB.BVIte _ _ c x y -> fmap SAWElt $ do
           tp <- SC.scBitvector sc (fromIntegral (natValue (bvWidth x)))
           join (SC.scIte sc tp <$> f c <*> f x <*> f y)
        SB.BVShl _ x y -> fmap SAWElt $ do
           let w = fromIntegral (widthVal (bvWidth x))
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvShl sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        SB.BVLshr _ x y -> fmap SAWElt $ do
           let w = fromIntegral (widthVal (bvWidth x))
           n <- SC.scNat sc w
           join (SC.scBvShr sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        SB.BVAshr _ x y -> fmap SAWElt $ do
           let w = fromIntegral (widthVal (bvWidth x))
           -- NB: bvSShr applies a `Succ` to its width argument, so we subtract
           --     1 here to make things match up.
           n <- SC.scNat sc (w - 1)
           join (SC.scBvSShr sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))

        SB.BVBitNot _ x -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           SC.scBvNot sc n =<< f x
        SB.BVBitAnd _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvAnd sc n <$> f x <*> f y)
        SB.BVBitOr _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvOr sc n <$> f x <*> f y)
        SB.BVBitXor _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvXor sc n <$> f x <*> f y)

        SB.BVConcat _ x y -> fmap SAWElt $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           m <- SC.scNat sc (fromIntegral (widthVal (bvWidth y)))
           t <- SC.scBoolType sc
           join (SC.scAppend sc t n m <$> f x <*> f y)
        SB.BVSelect start num x -> fmap SAWElt $ do
           i <- SC.scNat sc (fromIntegral (widthVal (bvWidth x) - widthVal num - widthVal start))
           n <- SC.scNat sc (fromIntegral (widthVal num))
           o <- SC.scNat sc (fromIntegral (widthVal start))
           t <- SC.scBoolType sc
           x' <- f x
           SC.scSlice sc t i n o x'
        SB.BVTrunc num x -> fmap SAWElt $ do
           let w = bvWidth x
           n <- SC.scNat sc (fromIntegral (widthVal num))
           m <- SC.scNat sc (fromIntegral (widthVal w - widthVal num))
           x' <- f x
           SC.scBvTrunc sc m n x'
        SB.BVZext w' x -> fmap SAWElt $ do
          let w = bvWidth x
          n <- SC.scNat sc (fromIntegral (widthVal w))
          m <- SC.scNat sc (fromIntegral (widthVal w' - widthVal w))
          x' <- f x
          SC.scBvUExt sc m n x'
        SB.BVSext w' x -> fmap SAWElt $ do
          let w = bvWidth x
          -- NB: width - 1 to make SAWCore types work out
          n <- SC.scNat sc (fromIntegral (widthVal w - 1))
          m <- SC.scNat sc (fromIntegral (widthVal w' - widthVal w))
          x' <- f x
          SC.scBvSExt sc m n x'

        SB.ArrayMap{} -> fail "FIXME SAW backend does not support ArrayMap."

        SB.ConstantArray indexTypes _range v -> fmap SAWElt $ do
          case Ctx.viewAssign indexTypes of
            Ctx.AssignExtend b dom -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."

              ty <- baseSCType sc dom
              v' <- SC.incVars sc 0 1 =<< f v
              --v' <- f v
              SC.scLambda sc "_" ty v'

        SB.SelectArray _ arr indexTerms -> fmap SAWElt $ do
          case Ctx.viewAssign indexTerms of
            Ctx.AssignExtend b idx -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."

              join $ SC.scApply sc <$> f arr <*> f idx

        SB.MuxArray indexTypes range p x y -> fmap SAWElt $ do
          case Ctx.viewAssign indexTypes of
            Ctx.AssignExtend b dom -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."
              domTy   <- baseSCType sc dom
              rangeTy <- baseSCType sc range
              ty <- SC.scFun sc domTy rangeTy
              join $ SC.scIte sc ty <$> f p <*> f x <*> f y

        SB.UpdateArray range _ arr indexTerms v -> fmap SAWElt $ do
          rangeTy <- baseSCType sc range
          arr' <- f arr
          v'   <- f v
          case Ctx.viewAssign indexTerms of
            Ctx.AssignExtend b idx -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."
              idx' <- f idx
              case exprType idx of
                BaseNatRepr -> do
                  SC.scUpdNatFun sc rangeTy arr' idx' v'
                BaseBVRepr w -> do
                  n <- SC.scNat sc (fromIntegral (natValue w))
                  SC.scUpdBvFun sc n rangeTy arr' idx' v'
                _ -> do
                  fail $ "SAWCore backend only currently supports integer and bitvector indices."

        SB.NatDiv{} -> nyi -- FIXME
        SB.NatToInteger x -> SAWElt <$> (SC.scNatToInt sc =<< f x)
        SB.IntegerToNat{} -> nyi -- FIXME
        SB.IntegerToReal x -> IntToRealSAWElt . SAWElt <$> f x
        SB.RealToInteger{} -> nyi -- FIXME
        SB.BVToInteger{} -> nyi -- FIXME
        SB.IntegerToSBV{} -> nyi -- FIXME
        SB.SBVToInteger{} -> nyi -- FIXME
        SB.IntegerToBV{} -> nyi -- FIXME
        SB.RoundReal{} -> nyi -- FIXME
        SB.FloorReal{} -> nyi -- FIXME
        SB.CeilReal{} -> nyi -- FIXME
        SB.Cplx{} -> nyi -- FIXME
        SB.RealPart{} -> nyi -- FIXME
        SB.ImagPart{} -> nyi -- FIXME
        SB.StructCtor{} -> nyi -- FIXME
        SB.StructField{} -> nyi -- FIXME
        SB.StructIte{} -> nyi -- FIXME

-- | The current location in the program.
assertions :: Simple Lens (SAWCoreState n) (Seq.Seq (Assertion (Pred (SAWCoreBackend n))))
assertions = lens saw_assertions (\s v -> s { saw_assertions = v })

-- | The sequence of accumulated assertion obligations
proofObligs :: Simple Lens (SAWCoreState n) (Seq (Seq (Pred (SAWCoreBackend n)), Assertion (Pred (SAWCoreBackend n))))
proofObligs = lens saw_obligations (\s v -> s { saw_obligations = v })

appendAssertion :: ProgramLoc
                -> Pred (SAWCoreBackend n)
                -> SimErrorReason
                -> SAWCoreState n
                -> SAWCoreState n
appendAssertion l p m s =
  let ast = Assertion l p (Just m) in
  s & assertions %~ (Seq.|> ast)
    & proofObligs %~ (Seq.|> (fmap (^.assertPred) (s^.assertions), ast))

-- | Append assertions to path state.
appendAssertions :: Seq (Assertion (Pred (SAWCoreBackend n)))
                 -> SAWCoreState n
                 -> SAWCoreState n
appendAssertions pairs = assertions %~ (Seq.>< pairs)

appendAssumption :: ProgramLoc
                 -> Pred (SAWCoreBackend n)
                 -> SAWCoreState n
                 -> SAWCoreState n
appendAssumption l p s =
  s & assertions %~ (Seq.|> Assertion l p Nothing)

checkSatisfiable :: SAWCoreBackend n
                 -> (Pred (SAWCoreBackend n))
                 -> IO (SatResult ())
checkSatisfiable sym p = do
  mgr <- readIORef (SB.sbStateManager sym)
  let cfg = saw_config mgr
      sc = saw_ctx mgr
      cache = saw_elt_cache mgr
  enabled <- getConfigValue sawCheckPathSat cfg
  case enabled of
    True -> do
      t <- evaluateElt sym sc cache p
      let bbPrims = const Map.empty
      BBSim.withBitBlastedPred GIA.proxy sc bbPrims t $ \be lit _shapes -> do
        satRes <- AIG.checkSat be lit
        case satRes of
          AIG.Unsat -> return Unsat
          _ -> return (Sat ())
    False -> return (Sat ())

instance SB.IsSimpleBuilderState SAWCoreState where
  sbAddAssumption sym e = do
    case SB.asApp e of
      Just SB.TrueBool -> return ()
      _ -> do
        loc <- getCurrentProgramLoc sym
        modifyIORef' (SB.sbStateManager sym) $ appendAssumption loc e

  sbAddAssertion sym e m = do
    case SB.asApp e of
      Just SB.TrueBool -> return ()
      Just SB.FalseBool -> do
        loc <- getCurrentProgramLoc sym
        throw (SimError loc m)
      _ -> do
        loc <- getCurrentProgramLoc sym
        modifyIORef' (SB.sbStateManager sym) $ appendAssertion loc e m

  sbAppendAssertions sym s = do
    modifyIORef' (SB.sbStateManager sym) $ appendAssertions s

  sbAssertionsBetween old cur =
    assert (old_cnt <= Seq.length a) $ Seq.drop old_cnt a
    where a = cur^.assertions
          old_cnt = Seq.length $ old^.assertions

  sbAllAssertions sym = do
    s <- readIORef (SB.sbStateManager sym)
    andAllOf sym folded (view assertPred <$> s^.assertions)

  sbEvalBranch sym pb = do
    case asConstantPred pb of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing -> do
        pb_neg <- notPred sym pb
        p_prior <- SB.sbAllAssertions sym
        p <- andPred sym p_prior pb
        p_neg <- andPred sym p_prior pb_neg
        p_res    <- checkSatisfiable sym p
        notp_res <- checkSatisfiable sym p_neg
        case (p_res, notp_res) of
          (Unsat, Unsat) -> return InfeasibleBranch
          (Unsat, _ )    -> return $! NoBranch False
          (_    , Unsat) -> return $! NoBranch True
          (_    , _)     -> return $! SymbolicBranch True

  sbGetProofObligations sym = do
    mg <- readIORef (SB.sbStateManager sym)
    return $ mg^.proofObligs

  sbSetProofObligations sym obligs = do
    modifyIORef' (SB.sbStateManager sym) (set proofObligs obligs)

  sbPushBranchPred sym p = SB.sbAddAssumption sym p
  sbBacktrackToState sym old =
    -- Copy assertions from old state to current state
    modifyIORef' (SB.sbStateManager sym) (set assertions (old ^. SB.pathState ^. assertions))
  sbSwitchToState sym _ new =
    -- Copy assertions from new state to current state
    modifyIORef' (SB.sbStateManager sym) (set assertions (new ^. SB.pathState ^. assertions))
