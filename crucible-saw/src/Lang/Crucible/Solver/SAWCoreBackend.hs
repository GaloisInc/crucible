-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.SAWCoreBackend2
-- Description      : Crucible interface for generating SAWCore
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides a crucible backend that produces SAWCore terms.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wwarn #-}

module Lang.Crucible.Solver.SAWCoreBackend2 where

import           Control.Exception ( assert, throw )
import           Control.Lens
import           Control.Monad
import           Data.IORef
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import qualified Lang.Crucible.Solver.SimpleBuilder as SB
import           Lang.Crucible.Solver.Symbol
import qualified Lang.Crucible.Solver.WeightedSum as WSum

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedAST as SC hiding (incVars)

-- | The SAWCoreBackend is a crucible backend that represents symbolic values
--   as SAWCore terms.
data SAWCoreState n
  = SAWCoreState
    { saw_ctx       :: SC.SharedContext                         -- ^ the main SAWCore datastructure for building shared terms
    , saw_inputs    :: IORef (Seq (SC.ExtCns SC.Term ))  -- ^ a record of all the symbolic input variables created so far,
                                                                  --   in the order they were created
    , saw_elt_cache :: SB.IdxCache n SAWElt
    , saw_assertions  :: Seq (Assertion (Pred (SAWCoreBackend n)))
    }

data SAWElt (bt :: BaseType) where
  SAWElt :: !SC.Term -> SAWElt bt

  -- This is a SAWCore term that represents an integer, but has an
  -- implicit integer-to-real conversion.
  IntToRealSAWElt :: !SC.Term -> SAWElt BaseRealType
  -- This is a SAWCore term that represents a natural number, but has an
  -- implicit nat-to-real conversion.
  NatToRealSAWElt :: !SC.Term -> SAWElt BaseRealType

type SAWCoreBackend n = SB.SimpleBuilder n SAWCoreState

baseSCType :: SC.SharedContext -> BaseTypeRepr tp -> IO SC.Term
baseSCType ctx bt =
  case bt of
    BaseBoolRepr -> SC.scBoolType ctx
    BaseBVRepr w -> SC.scBitvector ctx $ fromIntegral (natValue w)
    BaseNatRepr  -> SC.scNatType ctx
    BaseIntegerRepr -> SC.scInteger ctx
    BaseArrayRepr indexTypes range ->
      case Ctx.view indexTypes of
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

newSAWCoreBackend :: SC.SharedContext
                  -> NonceGenerator IO s
                  -> IO (SAWCoreBackend s)
newSAWCoreBackend sc gen = do
  inpr <- newIORef Seq.empty
  ch   <- SB.newIdxCache
  let st = SAWCoreState sc inpr ch Seq.empty
  SB.newSimpleBuilder st gen


-- | Run a computation with a fresh SAWCoreBackend, in the context of the
--   given module.
withSAWCoreBackend :: SC.Module -> (forall n. SAWCoreBackend n -> IO a) -> IO a
withSAWCoreBackend md f = do
  withIONonceGenerator $ \gen -> do
    sc   <- SC.mkSharedContext md
    sym  <- newSAWCoreBackend sc gen
    f sym

toSC :: SAWCoreBackend n -> SB.Elt n tp -> IO SC.Term
toSC sym elt = do
     st <- readIORef $ SB.sbStateManager sym
     evaluateElt sym (saw_ctx st) (saw_elt_cache st) elt

-- | Create a SAWCore term with type 'Integer' from a Haskell Integer.
scIntLit :: SC.SharedContext -> Integer -> IO SC.Term
scIntLit sc i
  | i >= 0 =
    SC.scNatToInt sc =<< SC.scNat sc (fromInteger i)
  | otherwise =
    SC.scIntNeg sc =<< SC.scNatToInt sc =<< SC.scNat sc (fromInteger (negate i))

-- | Return a shared term with type nat from a SAWElt.
scAsIntElt :: SC.SharedContext -> SAWElt BaseRealType -> IO SC.Term
scAsIntElt _ (IntToRealSAWElt t) = return t
scAsIntElt sc (NatToRealSAWElt t) = SC.scNatToInt sc t
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
    NatToRealSAWElt <$> SC.scNat sc (fromInteger (numerator r))
  | otherwise =
    IntToRealSAWElt <$> scIntLit sc (numerator r)

scAdd :: SC.SharedContext
      -> SAWElt BaseRealType
      -> SAWElt BaseRealType
      -> IO (SAWElt BaseRealType)
scAdd sc (NatToRealSAWElt x) (NatToRealSAWElt y) = fmap NatToRealSAWElt $
  SC.scAddNat sc x y
scAdd sc x y = fmap IntToRealSAWElt $
  join $ SC.scIntAdd sc <$> scAsIntElt sc x <*> scAsIntElt sc y

scMul :: SC.SharedContext
      -> SAWElt BaseRealType
      -> SAWElt BaseRealType
      -> IO (SAWElt BaseRealType)
scMul sc (NatToRealSAWElt x) (NatToRealSAWElt y) = do
  NatToRealSAWElt <$> SC.scMulNat sc x y
scMul sc x y = fmap IntToRealSAWElt $ do
  join $ SC.scIntMul sc <$> scAsIntElt sc x <*> scAsIntElt sc y

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
   go (SB.NatElt n _)  = SAWElt <$> SC.scNat sc (fromIntegral n)
   go (SB.IntElt _ _)  = fail "FIXME integer literals not supported"
   go (SB.RatElt _ _)  = fail "FIXME rational literals not supported"
   go (SB.BVElt w i _) = SAWElt <$> SC.scBvConst sc (fromIntegral (natValue w)) i

   go (SB.BoundVarElt bv) =
      case SB.bvarKind bv of
        SB.UninterpVarKind -> do
           tp <- baseSCType sc (SB.bvarType bv)
           SAWElt <$> sawCreateVar sym "x" tp
        SB.LatchVarKind ->
          fail $ unwords ["SAW backend does not support latch variables"]
        SB.QuantifierVarKind ->
          fail $ unwords ["SAW backend does not support quantifier variables"]

   go (SB.NonceAppElt p) =
      case SB.nonceEltApp p of
        SB.Forall _ _ ->
          fail "SAW backend does not support quantifiers"
        SB.Exists _ _ ->
          fail "SAW backend does not support quantifiers"

   go (SB.AppElt a) =
      case SB.eltApp a of

        SB.TrueBool  -> SAWElt <$> SC.scBool sc True
        SB.FalseBool -> SAWElt <$> SC.scBool sc False
        SB.NotBool x -> SAWElt <$> (SC.scNot sc =<< f x)
        SB.AndBool x y -> SAWElt <$> join (SC.scAnd sc <$> f x <*> f y)
        SB.XorBool x y -> SAWElt <$> join (SC.scXor sc <$> f x <*> f y)
        SB.IteBool c x y ->
            SAWElt <$> join (SC.scIte sc <$> SC.scBoolType sc <*> f c <*> f x <*> f y)

        SB.RealEq xe ye -> fmap SAWElt $ do
          xt <- eval xe
          yt <- eval ye
          case (xt, yt) of
            (NatToRealSAWElt xn, NatToRealSAWElt yn) -> do
              SC.scEqualNat sc xn yn
            _ -> do
              join $ SC.scIntEq sc <$> scAsIntElt sc xt <*> scAsIntElt sc yt
        SB.RealLe xe ye -> fmap SAWElt $ do
          xt <- eval xe
          yt <- eval ye
          case (xt, yt) of
            (NatToRealSAWElt xn, NatToRealSAWElt yn) -> do
              lt <- SC.scLtNat sc xn yn
              eq <- SC.scEqualNat sc xn yn
              SC.scOr sc lt eq
            _ -> do
              join $ SC.scIntLe sc <$> scAsIntElt sc xt <*> scAsIntElt sc yt
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

        SB.RealSum rs -> WSum.eval add smul (scRealLit sc) rs
          where add mx my = join $ scAdd sc <$> mx <*> my
                smul sm e = join $ scMul sc <$> scRealLit sc sm <*> eval e
        SB.RealMul x y ->
          join $ scMul sc <$> eval x <*> eval y

        SB.RealIte c xe ye -> do
          xt <- eval xe
          yt <- eval ye
          case (xt, yt) of
            (NatToRealSAWElt xn, NatToRealSAWElt yn) -> fmap NatToRealSAWElt $
              join (SC.scIte sc <$> SC.scNatType sc <*> f c ?? xn ?? yn)
            (IntToRealSAWElt xi, IntToRealSAWElt yi) -> fmap IntToRealSAWElt $
              join (SC.scIte sc <$> SC.scInteger sc <*> f c ?? xi ?? yi)
            _ -> realFail

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
          case Ctx.view indexTypes of
            Ctx.AssignExtend b dom -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."

              ty <- baseSCType sc dom
              v' <- SC.incVars sc 0 1 =<< f v
              --v' <- f v
              SC.scLambda sc "_" ty v'

        SB.SelectArray _ arr indexTerms -> fmap SAWElt $ do
          case Ctx.view indexTerms of
            Ctx.AssignExtend b idx -> do
              when (not (Ctx.null b)) $ do
                fail $ "SAW backend only supports single element arrays."

              join $ SC.scApply sc <$> f arr <*> f idx

        SB.MuxArray indexTypes range p x y -> fmap SAWElt $ do
          case Ctx.view indexTypes of
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
          case Ctx.view indexTerms of
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

-- | The current location in the program.
assertions :: Simple Lens (SAWCoreState n) (Seq.Seq (Assertion (Pred (SAWCoreBackend n))))
assertions = lens saw_assertions (\s v -> s { saw_assertions = v })

appendAssertion :: ProgramLoc
                -> Pred (SAWCoreBackend n)
                -> SimErrorReason
                -> SAWCoreState n
                -> SAWCoreState n
appendAssertion l p m s =
  s & assertions %~ (Seq.|> Assertion l p (Just m))

-- | Append assertions to path state.
appendAssertions :: Seq (Assertion (Pred (SAWCoreBackend n)))
                 -> SAWCoreState n
                 -> SAWCoreState n
appendAssertions pairs = assertions %~ (Seq.>< pairs)


instance SB.IsSimpleBuilderState SAWCoreState where
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

  sbEvalBranch _ p = do
    case asConstantPred p of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing    -> return $! SymbolicBranch True

  sbPushBranchPred _ _ = return ()
  sbBacktrackToState _ _ = return ()
  sbSwitchToState  _ _ _ = return ()
