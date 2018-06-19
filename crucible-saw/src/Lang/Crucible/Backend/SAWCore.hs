-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Backend.SAWCore
-- Description      : Crucible interface for generating SAWCore
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides a Crucible backend that produces SAWCore terms.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.Backend.SAWCore where

import           Control.Exception ( bracket )
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

import qualified Data.AIG as AIG
import           Numeric.Natural

import           What4.BaseTypes
import           What4.Config
import           What4.Concrete
import           What4.Interface
import           What4.SatResult
import qualified What4.Expr.Builder as B
import qualified What4.Expr.WeightedSum as WSum
import           What4.Symbol

import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Simulator.SimError

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Simulator.BitBlast as BBSim
import qualified Verifier.SAW.TypedAST as SC

data SAWCruciblePersonality sym = SAWCruciblePersonality

data AIGProxy where
  AIGProxy :: (AIG.IsAIG l g) => AIG.Proxy l g -> AIGProxy

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

    , saw_elt_cache :: B.IdxCache n SAWExpr

    , saw_assumptions :: AssumptionStack (B.BoolExpr n) AssumptionReason SimError
    , saw_aig_proxy :: AIGProxy
    }

sawCheckPathSat :: ConfigOption BaseBoolType
sawCheckPathSat = configOption BaseBoolRepr "saw.check_path_sat"

sawOptions :: [ConfigDesc]
sawOptions =
  [ opt sawCheckPathSat (ConcreteBool False)
    "Check the satisfiability of path conditions on branches"
  ]

getAssumptionStack :: SAWCoreBackend n -> IO (AssumptionStack (B.BoolExpr n) AssumptionReason SimError)
getAssumptionStack sym = saw_assumptions <$> readIORef (B.sbStateManager sym)

data SAWExpr (bt :: BaseType) where
  SAWExpr :: !SC.Term -> SAWExpr bt

  -- This is a term that represents an integer, but has an
  -- implicit integer-to-real conversion.
  IntToRealSAWExpr :: !(SAWExpr BaseIntegerType) -> SAWExpr BaseRealType
  -- This is a SAWCore term that represents a natural number, but has an
  -- implicit nat-to-integer conversion.
  NatToIntSAWExpr :: !(SAWExpr BaseNatType) -> SAWExpr BaseIntegerType

type SAWCoreBackend n = B.ExprBuilder n SAWCoreState


-- | Run the given IO action with the given SAW backend.
--   While while running the action, the SAW backend is
--   set up with a fresh naming context.  This means that all
--   symbolic inputs, symMap entries, element cache entires,
--   assertions and proof obligations start empty while
--   running the action.  After the action completes, the
--   state of these fields is restored.
inFreshNamingContext :: SAWCoreBackend n -> IO a -> IO a
inFreshNamingContext sym f =
  do old <- readIORef (B.sbStateManager sym)
     bracket (mkNew (B.exprCounter sym) old) (restore old) action

 where
 action new =
   do writeIORef (B.sbStateManager sym) new
      f

 restore old _new =
   do writeIORef (B.sbStateManager sym) old

 mkNew gen old =
   do ch <- B.newIdxCache
      iref <- newIORef mempty
      stk <- initAssumptionStack gen
      let new = SAWCoreState
                { saw_ctx = saw_ctx old
                , saw_inputs = iref
                , saw_symMap = mempty
                , saw_elt_cache = ch
                , saw_assumptions = stk
                , saw_aig_proxy = saw_aig_proxy old
                }
      return new

getInputs :: SAWCoreBackend n -> IO (Seq (SC.ExtCns SC.Term))
getInputs sym =
  do st <- readIORef (B.sbStateManager sym)
     readIORef (saw_inputs st)

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
    BaseStringRepr   -> fail "SAW backend does not support string values: baseSCType"
    BaseComplexRepr  -> fail "SAW backend does not support complex values: baseSCType"
    BaseRealRepr     -> fail "SAW backend does not support real values: baseSCType"
    BaseStructRepr _ -> fail "FIXME baseSCType for structures"

-- | Create a new symbolic variable.
sawCreateVar :: SAWCoreBackend n
             -> String                                       -- ^ the name of the variable
             -> SC.Term
             -> IO SC.Term
sawCreateVar sym nm tp = do
  st <- readIORef (B.sbStateManager sym)
  let sc = saw_ctx st
  i <- SC.scFreshGlobalVar sc
  let ec = SC.EC i ("var_"++nm++"_"++show i) tp
  t <- SC.scFlatTermF sc (SC.ExtCns ec)
  modifyIORef (saw_inputs st) (\xs -> xs Seq.|> ec)
  return t

bindSAWTerm :: SAWCoreBackend n
            -> BaseTypeRepr bt
            -> SC.Term
            -> IO (B.Expr n bt)
bindSAWTerm sym bt t = do
  st <- readIORef $ B.sbStateManager sym
  sbVar@(B.BoundVarExpr bv) <- freshConstant sym emptySymbol bt
  B.insertIdxValue (saw_elt_cache st) (B.bvarId bv) (SAWExpr t)
  return sbVar

newSAWCoreBackend ::
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SC.SharedContext ->
  NonceGenerator IO s ->
  IO (SAWCoreBackend s)
newSAWCoreBackend proxy sc gen = do
  inpr <- newIORef Seq.empty
  ch   <- B.newIdxCache
  stk  <- initAssumptionStack gen
  let st = SAWCoreState
              { saw_ctx = sc
              , saw_inputs = inpr
              , saw_symMap = Map.empty
              , saw_elt_cache = ch
              , saw_assumptions = stk
              , saw_aig_proxy = AIGProxy proxy
              }
  sym <- B.newExprBuilder st gen
  extendConfig sawOptions (getConfiguration sym)
  return sym


-- | Register an interpretation for a symbolic function.
-- This is not used during simulation, but rather, when we translate
-- crucible values back into SAW.
sawRegisterSymFunInterp ::
  SAWCoreBackend n ->
  B.ExprSymFn n args ret ->
  (SC.SharedContext -> [SC.Term] -> IO SC.Term) ->
  IO ()
sawRegisterSymFunInterp sym f i =
  modifyIORef (B.sbStateManager sym) $ \s ->
      s { saw_symMap = Map.insert (indexValue (B.symFnId f)) i (saw_symMap s) }


sawBackendSharedContext :: SAWCoreBackend n -> IO SC.SharedContext
sawBackendSharedContext sym =
  saw_ctx <$> readIORef (B.sbStateManager sym)


toSC :: SAWCoreBackend n -> B.Expr n tp -> IO SC.Term
toSC sym elt = do
     st <- readIORef $ B.sbStateManager sym
     evaluateExpr sym (saw_ctx st) (saw_elt_cache st) elt


-- | Return a shared term with type nat from a SAWExpr.
scAsIntExpr :: SC.SharedContext -> SAWExpr BaseRealType -> IO SC.Term
scAsIntExpr sc (IntToRealSAWExpr (NatToIntSAWExpr (SAWExpr t))) = SC.scNatToInt sc t
scAsIntExpr _ (IntToRealSAWExpr (SAWExpr t)) = return t
scAsIntExpr _ SAWExpr{} = fail $ "SAWbackend does not support real values."

-- | Create a Real SAWELT value from a Rational.
--
-- This fails on non-integer expressions.
scRealLit :: SC.SharedContext
          -> Rational
          -> IO (SAWExpr BaseRealType)
scRealLit sc r
  | denominator r /= 1 =
    fail "SAW backend does not support real values"
  | r >= 0 =
    IntToRealSAWExpr . NatToIntSAWExpr . SAWExpr <$> SC.scNat sc (fromInteger (numerator r))
  | otherwise =
    IntToRealSAWExpr <$> scIntLit sc (numerator r)

-- | Create a SAWCore term with type 'Integer' from a Haskell Integer.
scIntLit :: SC.SharedContext -> Integer -> IO (SAWExpr BaseIntegerType)
scIntLit sc i
  | i >= 0 =
    SAWExpr <$> (SC.scNatToInt sc =<< SC.scNat sc (fromInteger i))
  | otherwise =
    SAWExpr <$> (SC.scIntNeg sc =<< SC.scNatToInt sc =<< SC.scNat sc (fromInteger (negate i)))

-- | Create a SAWCore term with type 'Nat' from a Haskell Nat.
scNatLit :: SC.SharedContext -> Natural -> IO (SAWExpr BaseNatType)
scNatLit sc n = SAWExpr <$> SC.scNat sc (fromIntegral n)


scRealCmpop :: (SC.SharedContext -> SAWExpr BaseIntegerType -> SAWExpr BaseIntegerType -> IO (SAWExpr BaseBoolType))
            -> SC.SharedContext
            -> SAWExpr BaseRealType
            -> SAWExpr BaseRealType
            -> IO (SAWExpr BaseBoolType)
scRealCmpop intOp sc (IntToRealSAWExpr x) (IntToRealSAWExpr y) =
  intOp sc x y
scRealCmpop _ _ _ _ =
  fail "SAW backend does not support real values"

scRealBinop :: (SC.SharedContext -> SAWExpr BaseIntegerType -> SAWExpr BaseIntegerType -> IO (SAWExpr BaseIntegerType))
            -> SC.SharedContext
            -> SAWExpr BaseRealType
            -> SAWExpr BaseRealType
            -> IO (SAWExpr BaseRealType)
scRealBinop intOp sc (IntToRealSAWExpr x) (IntToRealSAWExpr y) =
  IntToRealSAWExpr <$> intOp sc x y
scRealBinop _ _ _ _ =
  fail "SAW backend does not support real values"


scIntBinop :: (SC.SharedContext -> SAWExpr BaseNatType -> SAWExpr BaseNatType -> IO (SAWExpr BaseNatType)) -- ^ operation on naturals
           -> (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) -- ^ operation on integers
           -> SC.SharedContext
           -> SAWExpr BaseIntegerType
           -> SAWExpr BaseIntegerType
           -> IO (SAWExpr BaseIntegerType)
scIntBinop natOp _intOp sc (NatToIntSAWExpr x) (NatToIntSAWExpr y) =
  NatToIntSAWExpr <$> natOp sc x y
scIntBinop _natOp intOp sc (NatToIntSAWExpr (SAWExpr x)) (SAWExpr y) =
  SAWExpr <$> join (intOp sc <$> SC.scNatToInt sc x <*> pure y)
scIntBinop _natOp intOp sc (SAWExpr x) (NatToIntSAWExpr (SAWExpr y)) =
  SAWExpr <$> join (intOp sc <$> pure x <*> SC.scNatToInt sc y)
scIntBinop _natOp intOp sc (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> intOp sc x y

scIntCmpop :: (SC.SharedContext -> SAWExpr BaseNatType -> SAWExpr BaseNatType -> IO (SAWExpr BaseBoolType)) -- ^ operation on naturals
           -> (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) -- ^ operation on integers
           -> SC.SharedContext
           -> SAWExpr BaseIntegerType
           -> SAWExpr BaseIntegerType
           -> IO (SAWExpr BaseBoolType)
scIntCmpop natOp _intOp sc (NatToIntSAWExpr x) (NatToIntSAWExpr y) =
  natOp sc x y
scIntCmpop _natOp intOp sc (NatToIntSAWExpr (SAWExpr x)) (SAWExpr y) =
  SAWExpr <$> join (intOp sc <$> SC.scNatToInt sc x <*> pure y)
scIntCmpop _natOp intOp sc (SAWExpr x) (NatToIntSAWExpr (SAWExpr y)) =
  SAWExpr <$> join (intOp sc <$> pure x <*> SC.scNatToInt sc y)
scIntCmpop _natOp intOp sc (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> intOp sc x y

scAddReal :: SC.SharedContext
          -> SAWExpr BaseRealType
          -> SAWExpr BaseRealType
          -> IO (SAWExpr BaseRealType)
scAddReal = scRealBinop scAddInt

scAddInt :: SC.SharedContext
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scAddInt = scIntBinop scAddNat SC.scIntAdd

scAddNat :: SC.SharedContext
            -> SAWExpr BaseNatType
            -> SAWExpr BaseNatType
            -> IO (SAWExpr BaseNatType)
scAddNat sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scAddNat sc x y


scMulReal :: SC.SharedContext
             -> SAWExpr BaseRealType
             -> SAWExpr BaseRealType
             -> IO (SAWExpr BaseRealType)
scMulReal = scRealBinop scMulInt

scMulInt :: SC.SharedContext
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scMulInt = scIntBinop scMulNat SC.scIntMul

scMulNat :: SC.SharedContext
            -> SAWExpr BaseNatType
            -> SAWExpr BaseNatType
            -> IO (SAWExpr BaseNatType)
scMulNat sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scMulNat sc x y

scIteReal :: SC.SharedContext
             -> SC.Term
             -> SAWExpr BaseRealType
             -> SAWExpr BaseRealType
             -> IO (SAWExpr BaseRealType)
scIteReal sc p = scRealBinop (\sc' -> scIteInt sc' p) sc

scIteInt :: SC.SharedContext
            -> SC.Term
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scIteInt sc p = scIntBinop
    (\sc' -> scIteNat sc' p)
    (\sc' x y -> SC.scIntegerType sc >>= \tp -> SC.scIte sc' tp p x y)
    sc

scIteNat :: SC.SharedContext
            -> SC.Term
            -> SAWExpr BaseNatType
            -> SAWExpr BaseNatType
            -> IO (SAWExpr BaseNatType)
scIteNat sc p (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> (SC.scNatType sc >>= \tp -> SC.scIte sc tp p x y)


scRealEq :: SC.SharedContext
         -> SAWExpr BaseRealType
         -> SAWExpr BaseRealType
         -> IO (SAWExpr BaseBoolType)
scRealEq = scRealCmpop scIntEq

scIntEq :: SC.SharedContext
        -> SAWExpr BaseIntegerType
        -> SAWExpr BaseIntegerType
        -> IO (SAWExpr BaseBoolType)
scIntEq = scIntCmpop scNatEq SC.scIntEq

scNatEq :: SC.SharedContext
        -> SAWExpr BaseNatType
        -> SAWExpr BaseNatType
        -> IO (SAWExpr BaseBoolType)
scNatEq sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scEqualNat sc x y


scRealLe :: SC.SharedContext
         -> SAWExpr BaseRealType
         -> SAWExpr BaseRealType
         -> IO (SAWExpr BaseBoolType)
scRealLe = scRealCmpop scIntLe

scIntLe :: SC.SharedContext
        -> SAWExpr BaseIntegerType
        -> SAWExpr BaseIntegerType
        -> IO (SAWExpr BaseBoolType)
scIntLe = scIntCmpop scNatLe SC.scIntLe

scNatLe :: SC.SharedContext
        -> SAWExpr BaseNatType
        -> SAWExpr BaseNatType
        -> IO (SAWExpr BaseBoolType)
scNatLe sc (SAWExpr x) (SAWExpr y) =
  do lt <- SC.scLtNat sc x y
     eq <- SC.scEqualNat sc x y
     SAWExpr <$> SC.scOr sc lt eq


-- | Note: first element in the result is the right-most value in the assignment
evaluateAsgn ::
  SAWCoreBackend n ->
  SC.SharedContext ->
  B.IdxCache n SAWExpr ->
  Ctx.Assignment (B.Expr n) args ->
  IO [SC.Term]
evaluateAsgn sym sc cache xs =
  case xs of
    Ctx.Empty -> return []
    ys Ctx.:> x ->
      do v  <- evaluateExpr sym sc cache x
         vs <- evaluateAsgn sym sc cache ys
         return (v:vs)


evaluateExpr :: forall n tp
             . SAWCoreBackend n
            -> SC.SharedContext
            -> B.IdxCache n SAWExpr
            -> B.Expr n tp
            -> IO SC.Term
evaluateExpr sym sc cache = f
 where
   -- Evaluate the element, and expect the result to have the same type.
   f :: B.Expr n tp' -> IO SC.Term
   f elt = do
       st <- eval elt
       case st of
         SAWExpr t -> return t
         _ -> realFail

   eval :: B.Expr n tp' -> IO (SAWExpr tp')
   eval elt = B.idxCacheEval cache elt (go elt)

   realFail :: IO a
   realFail = fail "SAW backend does not support real values"

   go :: B.Expr n tp' -> IO (SAWExpr tp')
   go (B.SemiRingLiteral sr x _) =
     case sr of
       B.SemiRingNat  -> SAWExpr <$> SC.scNat sc (fromIntegral x)
       B.SemiRingInt  -> scIntLit sc x
       B.SemiRingReal -> scRealLit sc x
   go (B.BVExpr w i _) = SAWExpr <$> SC.scBvConst sc (fromIntegral (natValue w)) i

   go (B.StringExpr{}) = fail "SAW backend does not support string values"

   go (B.BoundVarExpr bv) =
      case B.bvarKind bv of
        B.UninterpVarKind -> do
           tp <- baseSCType sc (B.bvarType bv)
           -- SAWExpr <$> sawCreateVar sym "x" tp
           SAWExpr <$> sawCreateVar sym nm tp
             where nm = Text.unpack $ solverSymbolAsText $ B.bvarName bv
        B.LatchVarKind ->
          fail $ unwords ["SAW backend does not support latch variables"]
        B.QuantifierVarKind ->
          fail $ unwords ["SAW backend does not support quantifier variables"]

   go (B.NonceAppExpr p) =
      case B.nonceExprApp p of
        B.Forall{} ->
          fail "SAW backend does not support quantifiers"
        B.Exists{} ->
          fail "SAW backend does not support quantifiers"
        B.ArrayFromFn{} ->
          fail "SAW backend does not support symbolic arrays"
        B.MapOverArrays{} ->
          fail "SAW backend does not support symbolic arrays"
        B.ArrayTrueOnEntries{} ->
          fail "SAW backend does not support symbolic arrays"
        B.FnApp fn asgn ->
          do st <- readIORef (B.sbStateManager sym)
             case Map.lookup (indexValue (B.symFnId fn)) (saw_symMap st) of
               Nothing -> fail ("Unknown symbolic function: " ++ show fn)
               Just mk ->
                 do ts <- evaluateAsgn sym sc cache asgn
                    SAWExpr <$> mk sc ts


   go a0@(B.AppExpr a) =
      let nyi :: Monad m => m a
          nyi = fail $ "Expression form not yet implemented in SAWCore backend:\n" ++ show a0 in
      case B.appExprApp a of

        B.TrueBool  -> SAWExpr <$> SC.scBool sc True
        B.FalseBool -> SAWExpr <$> SC.scBool sc False
        B.NotBool x -> SAWExpr <$> (SC.scNot sc =<< f x)
        B.AndBool x y -> SAWExpr <$> join (SC.scAnd sc <$> f x <*> f y)
        B.XorBool x y -> SAWExpr <$> join (SC.scXor sc <$> f x <*> f y)
        B.IteBool c x y ->
            SAWExpr <$> join (SC.scIte sc <$> SC.scBoolType sc <*> f c <*> f x <*> f y)

        B.SemiRingEq sr xe ye ->
          case sr of
            B.SemiRingReal -> join (scRealEq sc <$> eval xe <*> eval ye)
            B.SemiRingInt  -> join (scIntEq sc <$> eval xe <*> eval ye)
            B.SemiRingNat  -> join (scNatEq sc <$> eval xe <*> eval ye)

        B.SemiRingLe sr xe ye ->
          case sr of
            B.SemiRingReal -> join (scRealLe sc <$> eval xe <*> eval ye)
            B.SemiRingInt  -> join (scIntLe sc <$> eval xe <*> eval ye)
            B.SemiRingNat  -> join (scNatLe sc <$> eval xe <*> eval ye)

        B.SemiRingIte sr c xe ye ->
          case sr of
            B.SemiRingReal -> join (scIteReal sc <$> f c <*> eval xe <*> eval ye)
            B.SemiRingInt  -> join (scIteInt  sc <$> f c <*> eval xe <*> eval ye)
            B.SemiRingNat  -> join (scIteNat  sc <$> f c <*> eval xe <*> eval ye)

        B.SemiRingMul sr xe ye ->
           case sr of
             B.SemiRingReal -> join (scMulReal sc <$> eval xe <*> eval ye)
             B.SemiRingInt  -> join (scMulInt  sc <$> eval xe <*> eval ye)
             B.SemiRingNat  -> join (scMulNat  sc <$> eval xe <*> eval ye)

        B.SemiRingSum sr ss ->
          case sr of
            B.SemiRingReal -> WSum.eval add smul (scRealLit sc) ss
               where add mx my = join $ scAddReal sc <$> mx <*> my
                     smul sm e = join $ scMulReal sc <$> scRealLit sc sm <*> eval e
            B.SemiRingInt  -> WSum.eval add smul (scIntLit sc) ss
               where add mx my = join $ scAddInt sc <$> mx <*> my
                     smul sm e = join $ scMulInt sc <$> scIntLit sc sm <*> eval e
            B.SemiRingNat  -> WSum.eval add smul (scNatLit sc) ss
               where add mx my = join $ scAddNat sc <$> mx <*> my
                     smul sm e = join $ scMulNat sc <$> scNatLit sc sm <*> eval e

        B.RealIsInteger{} -> fail "SAW backend does not support real values"

        B.BVTestBit i bv -> fmap SAWExpr $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth bv)))
             bit <- SC.scBoolType sc
             join (SC.scAt sc w bit <$> f bv <*> SC.scNat sc (fromIntegral i))
        B.BVEq x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth x)))
             join (SC.scBvEq sc w <$> f x <*> f y)
        B.BVSlt x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth x)))
             join (SC.scBvSLt sc w <$> f x <*> f y)
        B.BVUlt x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (fromIntegral (natValue (bvWidth x)))
             join (SC.scBvULt sc w <$> f x <*> f y)

        B.ArrayEq _ _ -> fail "SAW backend does not support array equality"

        B.RealDiv{} -> realFail
        B.IntMod x y -> fmap SAWExpr $
          join (SC.scIntMod sc <$> f x <*> f y)
        B.RealSqrt{} -> realFail
        B.Pi{} -> realFail
        B.RealSin{} -> realFail
        B.RealCos{} -> realFail
        B.RealSinh{} -> realFail
        B.RealCosh{} -> realFail
        B.RealExp{} -> realFail
        B.RealLog{} -> realFail
        B.RealATan2{} -> realFail

        B.BVUnaryTerm{} -> fail "SAW backend does not support the unary bitvector representation"

        B.BVNeg _ x -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           SC.scBvNeg sc n =<< f x
        B.BVAdd _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvAdd sc n <$> f x <*> f y)
        B.BVMul _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvMul sc n <$> f x <*> f y)
        B.BVUdiv _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvUDiv sc n <$> f x <*> f y)
        B.BVUrem _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvURem sc n <$> f x <*> f y)
        B.BVSdiv _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvSDiv sc n <$> f x <*> f y)
        B.BVSrem _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvSRem sc n <$> f x <*> f y)
        B.BVIte _ _ c x y -> fmap SAWExpr $ do
           tp <- SC.scBitvector sc (fromIntegral (natValue (bvWidth x)))
           join (SC.scIte sc tp <$> f c <*> f x <*> f y)
        B.BVShl _ x y -> fmap SAWExpr $ do
           let w = fromIntegral (widthVal (bvWidth x))
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvShl sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        B.BVLshr _ x y -> fmap SAWExpr $ do
           let w = fromIntegral (widthVal (bvWidth x))
           n <- SC.scNat sc w
           join (SC.scBvShr sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        B.BVAshr _ x y -> fmap SAWExpr $ do
           let w = fromIntegral (widthVal (bvWidth x))
           -- NB: bvSShr applies a `Succ` to its width argument, so we subtract
           --     1 here to make things match up.
           n <- SC.scNat sc (w - 1)
           join (SC.scBvSShr sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))

        B.BVBitNot _ x -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           SC.scBvNot sc n =<< f x
        B.BVBitAnd _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvAnd sc n <$> f x <*> f y)
        B.BVBitOr _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvOr sc n <$> f x <*> f y)
        B.BVBitXor _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           join (SC.scBvXor sc n <$> f x <*> f y)

        B.BVConcat _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (fromIntegral (widthVal (bvWidth x)))
           m <- SC.scNat sc (fromIntegral (widthVal (bvWidth y)))
           t <- SC.scBoolType sc
           join (SC.scAppend sc t n m <$> f x <*> f y)
        B.BVSelect start num x -> fmap SAWExpr $ do
           i <- SC.scNat sc (fromIntegral (widthVal (bvWidth x) - widthVal num - widthVal start))
           n <- SC.scNat sc (fromIntegral (widthVal num))
           o <- SC.scNat sc (fromIntegral (widthVal start))
           t <- SC.scBoolType sc
           x' <- f x
           SC.scSlice sc t i n o x'
        B.BVTrunc num x -> fmap SAWExpr $ do
           let w = bvWidth x
           n <- SC.scNat sc (fromIntegral (widthVal num))
           m <- SC.scNat sc (fromIntegral (widthVal w - widthVal num))
           x' <- f x
           SC.scBvTrunc sc m n x'
        B.BVZext w' x -> fmap SAWExpr $ do
          let w = bvWidth x
          n <- SC.scNat sc (fromIntegral (widthVal w))
          m <- SC.scNat sc (fromIntegral (widthVal w' - widthVal w))
          x' <- f x
          SC.scBvUExt sc m n x'
        B.BVSext w' x -> fmap SAWExpr $ do
          let w = bvWidth x
          -- NB: width - 1 to make SAWCore types work out
          n <- SC.scNat sc (fromIntegral (widthVal w - 1))
          m <- SC.scNat sc (fromIntegral (widthVal w' - widthVal w))
          x' <- f x
          SC.scBvSExt sc m n x'

        B.ArrayMap{} -> fail "FIXME SAW backend does not support ArrayMap."

        B.ConstantArray indexTypes _range v -> fmap SAWExpr $ do
          case Ctx.viewAssign indexTypes of
            Ctx.AssignExtend b dom -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."

              ty <- baseSCType sc dom
              v' <- SC.incVars sc 0 1 =<< f v
              --v' <- f v
              SC.scLambda sc "_" ty v'

        B.SelectArray _ arr indexTerms -> fmap SAWExpr $ do
          case Ctx.viewAssign indexTerms of
            Ctx.AssignExtend b idx -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."

              join $ SC.scApply sc <$> f arr <*> f idx

        B.MuxArray indexTypes range p x y -> fmap SAWExpr $ do
          case Ctx.viewAssign indexTypes of
            Ctx.AssignExtend b dom -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."
              domTy   <- baseSCType sc dom
              rangeTy <- baseSCType sc range
              ty <- SC.scFun sc domTy rangeTy
              join $ SC.scIte sc ty <$> f p <*> f x <*> f y

        B.UpdateArray range _ arr indexTerms v -> fmap SAWExpr $ do
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

        B.NatDiv{} -> nyi -- FIXME
        B.NatToInteger x -> SAWExpr <$> (SC.scNatToInt sc =<< f x)
        B.IntegerToNat{} -> nyi -- FIXME
        B.IntegerToReal x -> IntToRealSAWExpr . SAWExpr <$> f x
        B.RealToInteger{} -> nyi -- FIXME
        B.BVToNat{} -> nyi -- FIXME
        B.BVToInteger{} -> nyi -- FIXME
        B.IntegerToSBV{} -> nyi -- FIXME
        B.SBVToInteger{} -> nyi -- FIXME
        B.IntegerToBV{} -> nyi -- FIXME
        B.RoundReal{} -> nyi -- FIXME
        B.FloorReal{} -> nyi -- FIXME
        B.CeilReal{} -> nyi -- FIXME
        B.Cplx{} -> nyi -- FIXME
        B.RealPart{} -> nyi -- FIXME
        B.ImagPart{} -> nyi -- FIXME
        B.StructCtor{} -> nyi -- FIXME
        B.StructField{} -> nyi -- FIXME
        B.StructIte{} -> nyi -- FIXME

checkSatisfiable :: SAWCoreBackend n
                 -> (Pred (SAWCoreBackend n))
                 -> IO (SatResult ())
checkSatisfiable sym p = do
  mgr <- readIORef (B.sbStateManager sym)
  let sc = saw_ctx mgr
      cache = saw_elt_cache mgr
  AIGProxy proxy <- return (saw_aig_proxy mgr)
  enabled <- getMaybeOpt =<< getOptionSetting sawCheckPathSat (getConfiguration sym)
  case enabled of
    Just True -> do
      t <- evaluateExpr sym sc cache p
      let bbPrims = const Map.empty
      BBSim.withBitBlastedPred proxy sc bbPrims t $ \be lit _shapes -> do
        satRes <- AIG.checkSat be lit
        case satRes of
          AIG.Unsat -> return Unsat
          _ -> return (Sat ())
    _ -> return (Sat ())

instance IsBoolSolver (SAWCoreBackend n) where
  addProofObligation sym a = do
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      _          -> AS.addProofObligation a =<< getAssumptionStack sym

  addAssumption sym a = do
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      Just False -> abortExecBecause (AssumedFalse (a ^. labeledPredMsg))
      _ -> AS.assume a =<< getAssumptionStack sym

  addAssumptions sym ps = do
    stk <- getAssumptionStack sym
    AS.appendAssumptions ps stk

  getPathCondition sym = do
    stk <- getAssumptionStack sym
    ps <- AS.collectAssumptions stk
    andAllOf sym (folded.labeledPred) ps

  evalBranch sym p0 =
    case asConstantPred p0 of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing    ->
        do p0_neg   <- notPred sym p0
           p_prior  <- getPathCondition sym
           p        <- andPred sym p_prior p0
           p_neg    <- andPred sym p_prior p0_neg
           p_res    <- checkSatisfiable sym p
           notp_res <- checkSatisfiable sym p_neg
           case (p_res, notp_res) of
             (Unsat, Unsat) -> abortExecBecause InfeasibleBranch
             (Unsat, _ )    -> return $! NoBranch False
             (_    , Unsat) -> return $! NoBranch True
             (_    , _)     -> return $! SymbolicBranch True

  getProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  setProofObligations sym obligs = do
    stk <- getAssumptionStack sym
    AS.setProofObligations obligs stk

  pushAssumptionFrame sym = do
    stk <- getAssumptionStack sym
    AS.pushFrame stk

  popAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    frm <- AS.popFrame ident stk
    readIORef (assumeFrameCond frm)

  cloneAssumptionState sym = do
    stk <- getAssumptionStack sym
    AS.cloneAssumptionStack stk

  restoreAssumptionState sym stk = do
    modifyIORef' (B.sbStateManager sym)
      (\st -> st{ saw_assumptions = stk })
