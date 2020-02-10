------------------------------------------------------------------------
-- |
-- Module      : What4.Expr.GroundEval
-- Description : Computing ground values for expressions from solver assignments
-- Copyright   : (c) Galois, Inc 2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
--
-- Given a collection of assignments to the symbolic values appearing in
-- an expression, this module computes the ground value.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.Expr.GroundEval
  ( -- * Ground evaluation
    GroundValue
  , GroundValueWrapper(..)
  , GroundArray(..)
  , lookupArray
  , GroundEvalFn(..)
  , ExprRangeBindings

    -- * Internal operations
  , tryEvalGroundExpr
  , evalGroundExpr
  , evalGroundApp
  , evalGroundNonceApp
  , defaultValueForType
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Data.Bits
import           Data.List (foldl')
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Numeric.Natural

import           What4.BaseTypes
import           What4.Interface
import qualified What4.SemiRing as SR
import qualified What4.Expr.ArrayUpdateMap as AUM
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.Builder
import qualified What4.Expr.StringSeq as SSeq
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.Arithmetic ( roundAway, clz, ctz, rotateLeft, rotateRight )
import           What4.Utils.Complex
import           What4.Utils.StringLiteral


type family GroundValue (tp :: BaseType) where
  GroundValue BaseBoolType          = Bool
  GroundValue BaseNatType           = Natural
  GroundValue BaseIntegerType       = Integer
  GroundValue BaseRealType          = Rational
  GroundValue (BaseBVType w)        = Integer
  GroundValue (BaseFloatType fpp)   = Integer
  GroundValue BaseComplexType       = Complex Rational
  GroundValue (BaseStringType si)   = StringLiteral si
  GroundValue (BaseArrayType idx b) = GroundArray idx b
  GroundValue (BaseStructType ctx)  = Ctx.Assignment GroundValueWrapper ctx

-- | A function that calculates ground values for elements.
--   Clients of solvers should use the @groundEval@ function for computing
--   values in models.
newtype GroundEvalFn t fs = GroundEvalFn { groundEval :: forall tp . Expr t fs tp -> IO (GroundValue tp) }

-- | Function that calculates upper and lower bounds for real-valued elements.
--   This type is used for solvers (e.g., dReal) that give only approximate solutions.
type ExprRangeBindings t fs = RealExpr t fs -> IO (Maybe Rational, Maybe Rational)

-- | A newtype wrapper around ground value for use in a cache.
newtype GroundValueWrapper tp = GVW { unGVW :: GroundValue tp }

-- | A representation of a ground-value array.
data GroundArray idx b
  = ArrayMapping (Ctx.Assignment GroundValueWrapper idx -> IO (GroundValue b))
    -- ^ Lookup function for querying by index
  | ArrayConcrete (GroundValue b) (Map.Map (Ctx.Assignment IndexLit idx) (GroundValue b))
    -- ^ Default value and finite map of particular indices

-- | Look up an index in an ground array.
lookupArray :: Ctx.Assignment BaseTypeRepr idx
            -> GroundArray idx b
            -> Ctx.Assignment GroundValueWrapper idx
            -> IO (GroundValue b)
lookupArray _ (ArrayMapping f) i = f i
lookupArray tps (ArrayConcrete base m) i = return $ fromMaybe base (Map.lookup i' m)
  where i' = fromMaybe (error "lookupArray: not valid indexLits") $ Ctx.zipWithM asIndexLit tps i

asIndexLit :: BaseTypeRepr tp -> GroundValueWrapper tp -> Maybe (IndexLit tp)
asIndexLit BaseNatRepr    (GVW v) = return $ NatIndexLit v
asIndexLit (BaseBVRepr w) (GVW v) = return $ BVIndexLit w v
asIndexLit _ _ = Nothing

-- | Convert a real standardmodel val to a double.
toDouble :: Rational -> Double
toDouble = fromRational

fromDouble :: Double -> Rational
fromDouble = toRational

-- | Construct a default value for a given base type.
defaultValueForType :: BaseTypeRepr tp -> GroundValue tp
defaultValueForType tp =
  case tp of
    BaseBoolRepr    -> False
    BaseNatRepr     -> 0
    BaseBVRepr _    -> 0
    BaseIntegerRepr -> 0
    BaseRealRepr    -> 0
    BaseComplexRepr -> 0 :+ 0
    BaseStringRepr si -> stringLitEmpty si
    BaseArrayRepr _ b -> ArrayConcrete (defaultValueForType b) Map.empty
    BaseStructRepr ctx -> fmapFC (GVW . defaultValueForType) ctx
    BaseFloatRepr _ -> 0

{-# INLINABLE evalGroundExpr #-}
-- | Helper function for evaluating @Expr@ expressions in a model.
--
--   This function is intended for implementers of symbolic backends.
evalGroundExpr ::
  (forall u . Expr t fs u -> IO (GroundValue u)) ->
  Expr t fs tp ->
  IO (GroundValue tp)
evalGroundExpr f e =
 runMaybeT (tryEvalGroundExpr f e) >>= \case
    Nothing -> fail $ unwords ["evalGroundExpr: could not evaluate expression:", show e]
    Just x  -> return x

{-# INLINABLE tryEvalGroundExpr #-}
-- | Evaluate an element, when given an evaluation function for
--   subelements.  Instead of recursing directly, `tryEvalGroundExpr`
--   calls into the given function on sub-elements to allow the caller
--   to cache results if desired.
--
--   However, sometimes we are unable to compute expressions outside
--   the solver.  In these cases, this function will return `Nothing`
--   in the `MaybeT IO` monad.  In these cases, the caller should instead
--   query the solver directly to evaluate the expression, if possible.
tryEvalGroundExpr :: (forall u . Expr t fs u -> IO (GroundValue u))
                 -> Expr t fs tp
                 -> MaybeT IO (GroundValue tp)
tryEvalGroundExpr _ (SemiRingLiteral SR.SemiRingNatRepr c _) = return c
tryEvalGroundExpr _ (SemiRingLiteral SR.SemiRingIntegerRepr c _) = return c
tryEvalGroundExpr _ (SemiRingLiteral SR.SemiRingRealRepr c _) = return c
tryEvalGroundExpr _ (SemiRingLiteral (SR.SemiRingBVRepr _ _ ) c _) = return c
tryEvalGroundExpr _ (StringExpr x _) = return x
tryEvalGroundExpr _ (BoolExpr b _) = return b
tryEvalGroundExpr f (AnnotationExpr _ t _) = tryEvalGroundExpr f t
tryEvalGroundExpr f (NonceAppExpr a0) = evalGroundNonceApp (lift . f) (nonceExprApp a0)
tryEvalGroundExpr f (AppExpr a0)      = evalGroundApp f (appExprApp a0)
tryEvalGroundExpr _ (BoundVarExpr v) =
  case bvarKind v of
    QuantifierVarKind -> fail $ "The ground evaluator does not support bound variables."
    LatchVarKind      -> return $! defaultValueForType (bvarType v)
    UninterpVarKind   -> return $! defaultValueForType (bvarType v)

{-# INLINABLE evalGroundNonceApp #-}
-- | Helper function for evaluating @NonceApp@ expressions.
--
--   This function is intended for implementers of symbolic backends.
evalGroundNonceApp :: MonadFail m
                   => (forall u . Expr t fs u -> MaybeT m (GroundValue u))
                   -> NonceApp t fs (Expr t fs) tp
                   -> MaybeT m (GroundValue tp)
evalGroundNonceApp _ a0 = lift $ fail $
  case a0 of
    Forall{} -> "The ground evaluator does not support quantifiers."
    Exists{} -> "The ground evaluator does not support quantifiers."
    MapOverArrays{} -> "The ground evaluator does not support mapping arrays from arbitrary functions."
    ArrayFromFn{} -> "The ground evaluator does not support arrays from arbitrary functions."
    ArrayTrueOnEntries{} -> "The ground evaluator does not support arrayTrueOnEntries."
    FnApp{}  -> "The ground evaluator does not support function applications."

{-# INLINABLE evalGroundApp #-}

forallIndex :: Ctx.Size (ctx :: Ctx.Ctx k) -> (forall tp . Ctx.Index ctx tp -> Bool) -> Bool
forallIndex sz f = Ctx.forIndex sz (\b j -> f j && b) True


newtype MAnd x = MAnd { unMAnd :: Maybe Bool }
instance Functor MAnd where
  fmap _f (MAnd x) = MAnd x
instance Applicative MAnd where
  pure _ = MAnd (Just True)
  MAnd (Just a) <*> MAnd (Just b) = MAnd (Just $! (a && b))
  _ <*> _ = MAnd Nothing

mand :: Bool -> MAnd z
mand = MAnd . Just

coerceMAnd :: MAnd a -> MAnd b
coerceMAnd (MAnd x) = MAnd x


groundEq :: BaseTypeRepr tp -> GroundValue tp -> GroundValue tp -> MAnd z
groundEq bt x y = case bt of
  BaseBoolRepr    -> mand $ x == y
  BaseRealRepr    -> mand $ x == y
  BaseIntegerRepr -> mand $ x == y
  BaseNatRepr     -> mand $ x == y
  BaseBVRepr _    -> mand $ x == y
  BaseFloatRepr _ -> mand $ x == y
  BaseStringRepr _ -> mand $ x == y
  BaseComplexRepr -> mand $ x == y
  BaseStructRepr flds ->
    coerceMAnd (Ctx.traverseWithIndex
      (\i tp -> groundEq tp (unGVW (x Ctx.! i)) (unGVW (y Ctx.! i))) flds)
  BaseArrayRepr{} -> MAnd Nothing

-- | Helper function for evaluating @App@ expressions.
--
--   This function is intended for implementers of symbolic backends.
evalGroundApp :: forall t fs tp
               . (forall u . Expr t fs u -> IO (GroundValue u))
              -> App (Expr t fs) tp
              -> MaybeT IO (GroundValue tp)
evalGroundApp f0 a0 = do
  let f :: forall u . Expr t fs u -> MaybeT IO (GroundValue u)
      f = lift . f0
  case a0 of
    BaseEq bt x y ->
      do x' <- f x
         y' <- f y
         MaybeT (return (unMAnd (groundEq bt x' y')))

    BaseIte _ _ x y z -> do
      xv <- f x
      if xv then f y else f z

    NotPred x -> not <$> f x
    ConjPred xs ->
      let pol (x,Positive) = f x
          pol (x,Negative) = not <$> f x
      in
      case BM.viewBoolMap xs of
        BM.BoolMapUnit -> return True
        BM.BoolMapDualUnit -> return False
        BM.BoolMapTerms (t:|ts) ->
          foldl' (&&) <$> pol t <*> mapM pol ts

    RealIsInteger x -> (\xv -> denominator xv == 1) <$> f x
    BVTestBit i x -> assert (i <= fromIntegral (maxBound :: Int)) $
        (`testBit` (fromIntegral i)) <$> f x
    BVSlt x y -> (<) <$> (toSigned w <$> f x)
                     <*> (toSigned w <$> f y)
      where w = bvWidth x
    BVUlt x y -> (<) <$> f x <*> f y

    NatDiv x y -> g <$> f x <*> f y
      where g _ 0 = 0
            g u v = u `div` v

    NatMod x y -> g <$> f x <*> f y
      where g _ 0 = 0
            g u v = u `mod` v

    IntDiv x y -> g <$> f x <*> f y
      where
      g u v | v == 0    = 0
            | v >  0    = u `div` v
            | otherwise = negate (u `div` negate v)

    IntMod x y -> intModu <$> f x <*> f y
      where intModu _ 0 = 0
            intModu i v = fromInteger (i `mod` abs v)

    IntAbs x -> fromInteger . abs <$> f x

    IntDivisible x k -> g <$> f x
      where
      g u | k == 0    = u == 0
          | otherwise = mod u (toInteger k) == 0

    SemiRingLe SR.OrderedSemiRingRealRepr    x y -> (<=) <$> f x <*> f y
    SemiRingLe SR.OrderedSemiRingIntegerRepr x y -> (<=) <$> f x <*> f y
    SemiRingLe SR.OrderedSemiRingNatRepr     x y -> (<=) <$> f x <*> f y

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingNatRepr -> WSum.evalM (\x y -> pure (x+y)) smul pure s
           where smul sm e = (sm *) <$> f e
        SR.SemiRingIntegerRepr -> WSum.evalM (\x y -> pure (x+y)) smul pure s
           where smul sm e = (sm *) <$> f e
        SR.SemiRingRealRepr -> WSum.evalM (\x y -> pure (x+y)) smul pure s
           where smul sm e = (sm *) <$> f e
        SR.SemiRingBVRepr SR.BVArithRepr w -> WSum.evalM sadd smul pure s
           where
           smul sm e = toUnsigned w . (sm *) <$> f e
           sadd x y  = pure (toUnsigned w (x + y))
        SR.SemiRingBVRepr SR.BVBitsRepr _w -> WSum.evalM sadd smul pure s
           where
           smul sm e = (sm .&.) <$> f e
           sadd x y  = pure (x `xor` y)

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingNatRepr     -> fromMaybe 1 <$> WSum.prodEvalM (\x y -> pure (x*y)) f pd
        SR.SemiRingIntegerRepr -> fromMaybe 1 <$> WSum.prodEvalM (\x y -> pure (x*y)) f pd
        SR.SemiRingRealRepr    -> fromMaybe 1 <$> WSum.prodEvalM (\x y -> pure (x*y)) f pd
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          fromMaybe 1 <$> WSum.prodEvalM (\x y -> pure (toUnsigned w (x*y))) f pd
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          fromMaybe (maxUnsigned w) <$> WSum.prodEvalM (\x y -> pure (x .&. y)) f pd

    RealDiv x y -> do
      xv <- f x
      yv <- f y
      return $!
        if yv == 0 then 0 else xv / yv
    RealSqrt x -> do
      xv <- f x
      when (xv < 0) $ do
        lift $ fail $ "Model returned sqrt of negative number."
      return $ fromDouble (sqrt (toDouble xv))

    ------------------------------------------------------------------------
    -- Operations that introduce irrational numbers.

    Pi -> return $ fromDouble pi
    RealSin x -> fromDouble . sin . toDouble <$> f x
    RealCos x -> fromDouble . cos . toDouble <$> f x
    RealATan2 x y -> do
      xv <- f x
      yv <- f y
      return $ fromDouble (atan2 (toDouble xv) (toDouble yv))
    RealSinh x -> fromDouble . sinh . toDouble <$> f x
    RealCosh x -> fromDouble . cosh . toDouble <$> f x

    RealExp x -> fromDouble . exp . toDouble <$> f x
    RealLog x -> fromDouble . log . toDouble <$> f x

    ------------------------------------------------------------------------
    -- Bitvector Operations

    BVOrBits _w bs -> foldl' (.|.) 0 <$> traverse f (bvOrToList bs)
    BVUnaryTerm u -> do
      UnaryBV.evaluate f u
    BVConcat w x y -> cat <$> f x <*> f y
      where w2 = bvWidth y
            cat a b = toUnsigned w $ a `shiftL` (fromIntegral (natValue w2)) .|. b
    BVSelect idx n x -> sel <$> f x
      where sel a = toUnsigned n (a `shiftR` shft)
            shft = fromIntegral (natValue (bvWidth x) - natValue idx - natValue n)
    BVUdiv w x y -> toUnsigned w <$> (myDiv <$> f x <*> f y)
      where myDiv _ 0 = 0
            myDiv u v = u `div` v
    BVUrem w x y -> toUnsigned w <$> (myRem <$> f x <*> f y)
      where myRem u 0 = u
            myRem u v = u `rem` v
    BVSdiv w x y -> toUnsigned w <$> (myDiv <$> f x <*> f y)
      where myDiv _ 0 = 0
            myDiv u v = toSigned w u `div` toSigned w v
    BVSrem w x y -> toUnsigned w <$> (myRem <$> f x <*> f y)
      where myRem u 0 = u
            myRem u v = toSigned w u `rem` toSigned w v
    BVShl  w x y -> toUnsigned w <$> (shiftL <$> f x <*> (fromInteger <$> f y))
    BVLshr w x y -> lift $
      toUnsigned w <$> (shiftR <$> f0 x <*> (fromInteger <$> f0 y))
    BVAshr w x y -> lift $
      toUnsigned w <$> (shiftR <$> (toSigned w <$> f0 x) <*> (fromInteger <$> f0 y))

    BVRol w x y -> lift $ (rotateLeft w <$> f0 x <*> f0 y)
    BVRor w x y -> lift $ (rotateRight w <$> f0 x <*> f0 y)

    BVZext _ x -> lift $ f0 x
    BVSext w x -> lift $ do
      case isPosNat w of
        Just LeqProof -> (toUnsigned w . toSigned (bvWidth x)) <$> f0 x
        Nothing -> error "BVSext given bad width"

    BVFill w p ->
      do b <- f p
         return $! if b then maxUnsigned w else 0

    BVPopcount _w x ->
      toInteger . popCount <$> f x
    BVCountLeadingZeros w x ->
      clz w <$> f x
    BVCountTrailingZeros w x ->
      ctz w <$> f x

    ------------------------------------------------------------------------
    -- Bitvector Operations
    FloatPZero{}      -> MaybeT $ return Nothing
    FloatNZero{}      -> MaybeT $ return Nothing
    FloatNaN{}        -> MaybeT $ return Nothing
    FloatPInf{}       -> MaybeT $ return Nothing
    FloatNInf{}       -> MaybeT $ return Nothing
    FloatNeg{}        -> MaybeT $ return Nothing
    FloatAbs{}        -> MaybeT $ return Nothing
    FloatSqrt{}       -> MaybeT $ return Nothing
    FloatAdd{}        -> MaybeT $ return Nothing
    FloatSub{}        -> MaybeT $ return Nothing
    FloatMul{}        -> MaybeT $ return Nothing
    FloatDiv{}        -> MaybeT $ return Nothing
    FloatRem{}        -> MaybeT $ return Nothing
    FloatMin{}        -> MaybeT $ return Nothing
    FloatMax{}        -> MaybeT $ return Nothing
    FloatFMA{}        -> MaybeT $ return Nothing
    FloatFpEq{}       -> MaybeT $ return Nothing
    FloatFpNe{}       -> MaybeT $ return Nothing
    FloatLe{}         -> MaybeT $ return Nothing
    FloatLt{}         -> MaybeT $ return Nothing
    FloatIsNaN{}      -> MaybeT $ return Nothing
    FloatIsInf{}      -> MaybeT $ return Nothing
    FloatIsZero{}     -> MaybeT $ return Nothing
    FloatIsPos{}      -> MaybeT $ return Nothing
    FloatIsNeg{}      -> MaybeT $ return Nothing
    FloatIsSubnorm{}  -> MaybeT $ return Nothing
    FloatIsNorm{}     -> MaybeT $ return Nothing
    FloatCast{}       -> MaybeT $ return Nothing
    FloatRound{}      -> MaybeT $ return Nothing
    FloatFromBinary _ x -> f x
    FloatToBinary{}   -> MaybeT $ return Nothing
    BVToFloat{}       -> MaybeT $ return Nothing
    SBVToFloat{}      -> MaybeT $ return Nothing
    RealToFloat{}     -> MaybeT $ return Nothing
    FloatToBV{}       -> MaybeT $ return Nothing
    FloatToSBV{}      -> MaybeT $ return Nothing
    FloatToReal{}     -> MaybeT $ return Nothing

    ------------------------------------------------------------------------
    -- Array Operations

    ArrayMap idx_types _ m def -> lift $ do
      m' <- traverse f0 (AUM.toMap m)
      h <- f0 def
      return $ case h of
        ArrayMapping h' -> ArrayMapping $ \idx ->
          case (`Map.lookup` m') =<< Ctx.zipWithM asIndexLit idx_types idx of
            Just r ->  return r
            Nothing -> h' idx
        ArrayConcrete d m'' ->
          -- Map.union is left-biased
          ArrayConcrete d (Map.union m' m'')

    ConstantArray _ _ v -> lift $ do
      val <- f0 v
      return $ ArrayConcrete val Map.empty

    SelectArray _ a i -> do
      arr <- f a
      let arrIdxTps = case exprType a of
                        BaseArrayRepr idx _ -> idx
      idx <- traverseFC (\e -> GVW <$> f e) i
      lift $ lookupArray arrIdxTps arr idx

    UpdateArray _ idx_tps a i v -> do
      arr <- f a
      idx <- traverseFC (\e -> GVW <$> f e) i
      case arr of
        ArrayMapping arr' -> return . ArrayMapping $ \x ->
          if indicesEq idx_tps idx x then f0 v else arr' x
        ArrayConcrete d m -> do
          val <- f v
          let idx' = fromMaybe (error "UpdateArray only supported on Nat and BV") $ Ctx.zipWithM asIndexLit idx_tps idx
          return $ ArrayConcrete d (Map.insert idx' val m)

     where indicesEq :: Ctx.Assignment BaseTypeRepr ctx
                     -> Ctx.Assignment GroundValueWrapper ctx
                     -> Ctx.Assignment GroundValueWrapper ctx
                     -> Bool
           indicesEq tps x y =
             forallIndex (Ctx.size x) $ \j ->
               let GVW xj = x Ctx.! j
                   GVW yj = y Ctx.! j
                   tp = tps Ctx.! j
               in case tp of
                    BaseNatRepr  -> xj == yj
                    BaseBVRepr _ -> xj == yj
                    _ -> error $ "We do not yet support UpdateArray on " ++ show tp ++ " indices."

    ------------------------------------------------------------------------
    -- Conversions

    NatToInteger x -> toInteger <$> f x
    IntegerToReal x -> toRational <$> f x
    BVToNat x      -> fromInteger <$> f x
    BVToInteger x  -> f x
    SBVToInteger x -> toSigned (bvWidth x) <$> f x

    RoundReal x -> roundAway <$> f x
    FloorReal x -> floor <$> f x
    CeilReal  x -> ceiling <$> f x

    RealToInteger x -> floor <$> f x

    IntegerToNat x -> fromInteger . max 0 <$> f x
    IntegerToBV x w -> toUnsigned w <$> f x

    ------------------------------------------------------------------------
    -- Complex operations.

    Cplx (x :+ y) -> (:+) <$> f x <*> f y
    RealPart x -> realPart <$> f x
    ImagPart x -> imagPart <$> f x

    ------------------------------------------------------------------------
    -- String operations

    StringLength x -> stringLitLength <$> f x
    StringContains x y -> stringLitContains <$> f x <*> f y
    StringIsSuffixOf x y -> stringLitIsSuffixOf <$> f x <*> f y
    StringIsPrefixOf x y -> stringLitIsPrefixOf <$> f x <*> f y
    StringIndexOf x y k -> stringLitIndexOf <$> f x <*> f y <*> f k
    StringSubstring _ x off len -> stringLitSubstring <$> f x <*> f off <*> f len
    StringAppend si xs ->
      do let g x (SSeq.StringSeqLiteral l) = pure (x <> l)
             g x (SSeq.StringSeqTerm t)    = (x <>) <$> f t
         foldM g (stringLitEmpty si) (SSeq.toList xs)

    ------------------------------------------------------------------------
    -- Structs

    StructCtor _ flds -> do
      traverseFC (\v -> GVW <$> f v) flds
    StructField s i _ -> do
      sv <- f s
      return $! unGVW (sv Ctx.! i)
