------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Analysis.Shape
-- Description : A basic shape analysis phase on Crucible CFGs
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- This shape analysis tracks the flow of literal, concrete and symbolic
-- data through a program.  The main use for this analysis is to identify
-- which parts of the program do and do not depend on symbolic inputs,
-- and likewise which control-flow paths depend on symbolic branch conditions.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wwarn #-}
module Lang.Crucible.Analysis.Shape where

import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Parameterized.Context ( Assignment )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Text (Text)
import qualified Data.Vector as V
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Lang.MATLAB.CharVector as CV
import           Lang.MATLAB.FieldName
import           Lang.MATLAB.MatlabChar (MatlabChar)
import qualified Lang.MATLAB.MultiDimArray as MDA
import           Lang.MATLAB.Utils.Nat (Nat)

import           Lang.Crucible.Analysis.ForwardDataflow
import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.MATLAB.Types

import qualified Debug.Trace as Debug

type family ShapeLit (tp :: CrucibleType) :: * where
  ShapeLit BoolType = Bool
  ShapeLit NatType  = Nat
  ShapeLit IntegerType = Integer
  ShapeLit ArrayDimType = MDA.ArrayDim
  ShapeLit RealValType  = Rational
  ShapeLit (FunctionHandleType args ret) = FnHandle args ret
  ShapeLit CharType = MatlabChar
  ShapeLit StringType = Text
  ShapeLit (BVType w) = Integer

type family ArrayElts (tp::CrucibleType) :: CrucibleType where
  ArrayElts (MultiDimArrayType tp) = tp
  ArrayElts (SymbolicMultiDimArrayType bt) = BaseToType bt
  ArrayElts MatlabStructArrayType = MatlabStructType
  ArrayElts MatlabIntArrayType = MatlabIntType
  ArrayElts MatlabUIntArrayType = MatlabUIntType

data ShapeDom (tp :: CrucibleType) where
  SymbolicShape :: ShapeDom tp   -- top element of the domain (means that the value may depend on symbolic inputs)
  BotShape      :: ShapeDom tp   -- bottom element of the domain (means that no values flow to this position)

  -- concrete shapes
  ConcreteShape      :: ShapeDom tp    -- concrete value not known at analysis time
  LitShape           :: (Show (ShapeLit tp), Eq (ShapeLit tp))
                     => ShapeLit tp
                     -> ShapeDom tp   -- concrete value known at analysis time

  -- intermediate shapes
  ArrayShape         :: MDA.MultiDimArray (ShapeDom (ArrayElts tp))
                     -> ShapeDom tp
  IntShape           :: (1 <= w) => NatRepr w -> ShapeDom (BVType w) -> ShapeDom MatlabIntType
  UIntShape          :: NatRepr w -> ShapeDom (BVType w) -> ShapeDom MatlabUIntType
  ComplexShape       :: ShapeDom RealValType -> ShapeDom RealValType -> ShapeDom ComplexRealType
  MaybeShape         :: Bool -> ShapeDom tp -> ShapeDom (MaybeType tp)
  StructShape        :: Ctx.Assignment ShapeDom ctx -> ShapeDom (StructType ctx)
  MatlabStructShape  :: Map FieldName (ShapeDom MatlabValueType) -> ShapeDom MatlabStructType
  WordMapShape       :: NatRepr w -> Map Integer (ShapeDom (BaseToType tp)) -> ShapeDom (WordMapType w tp)
  VectorShape        :: V.Vector (ShapeDom tp) -> ShapeDom (VectorType tp)
  StringMapShape     :: Map Text (ShapeDom (MaybeType tp)) -> ShapeDom (StringMapType tp)
  MatlabValueShape   :: MSwitch ShapeDom -> ShapeDom MatlabValueType
  MatlabHandleShape  :: ShapeDom (FunctionHandleType MatlabFunctionBaseArgs MatlabFunctionReturnType)
                     -> Bool
                     -> Text
                     -> Int
                     -> ShapeDom MatlabHandleType


mapConcrete :: ShapeDom tp -> ShapeDom tp' -> ShapeDom tp'
mapConcrete BotShape _ = BotShape
mapConcrete ConcreteShape x = x
mapConcrete SymbolicShape _ = SymbolicShape
mapConcrete (LitShape _) x = x
mapConcrete (IntShape _ a) x = mapConcrete a x
mapConcrete (UIntShape _ a) x = mapConcrete a x
mapConcrete (ComplexShape a b) x = mapConcrete a (mapConcrete b x)
mapConcrete (MaybeShape b a) x = shapelub (if b then ConcreteShape else BotShape) (mapConcrete a x)
mapConcrete (MatlabValueShape sw) x =
  foldlF (\sh b -> shapelub sh (mapConcrete b ConcreteShape)) x sw
mapConcrete (ArrayShape a) x = foldr mapConcrete x a
mapConcrete (MatlabStructShape m) x = Map.foldr mapConcrete x m
mapConcrete (VectorShape a) x = V.foldr mapConcrete x a
mapConcrete (StringMapShape m) x = Map.foldr mapConcrete x m
mapConcrete (MatlabHandleShape h _ _ _) x = mapConcrete h x
mapConcrete (StructShape xs) x = foldrFC mapConcrete x xs
mapConcrete (WordMapShape _ m) x = Map.foldr mapConcrete x m

-- | Lift any concrete, but unknown, shapes to the symbolic shape,
--   while leaving structural information and literal values unchanged.
--   This function is used to account for symbolic control flow in the
--   shape analysis.
liftToSymbolic :: ShapeDom tp -> ShapeDom tp
liftToSymbolic BotShape = BotShape
liftToSymbolic ConcreteShape = SymbolicShape
liftToSymbolic SymbolicShape = SymbolicShape
liftToSymbolic (LitShape x)  = LitShape x
liftToSymbolic (ComplexShape r i) = ComplexShape (liftToSymbolic r) (liftToSymbolic i)
liftToSymbolic (MaybeShape b BotShape) = MaybeShape b BotShape
liftToSymbolic (MaybeShape False x) = MaybeShape False (liftToSymbolic x)
liftToSymbolic (MaybeShape True _) = SymbolicShape
liftToSymbolic (MatlabValueShape sw)
  | foldlF (\i r -> case r of BotShape -> i; _ -> i+1) 0 sw <= (1::Int)
      = MatlabValueShape (fmapF liftToSymbolic sw)
liftToSymbolic (MatlabValueShape _) = SymbolicShape
liftToSymbolic (VectorShape v) = VectorShape (V.map liftToSymbolic v)
liftToSymbolic (StringMapShape m) = StringMapShape $ Map.map liftToSymbolic m
liftToSymbolic (StructShape xs) = StructShape $ fmapFC liftToSymbolic xs
liftToSymbolic (ArrayShape a) = ArrayShape $ MDA.map liftToSymbolic a
liftToSymbolic (IntShape w x) = IntShape w $ liftToSymbolic x
liftToSymbolic (UIntShape w x) = UIntShape w $ liftToSymbolic x
liftToSymbolic (MatlabStructShape m) = MatlabStructShape $ Map.map liftToSymbolic m
liftToSymbolic (MatlabHandleShape x b i n) = MatlabHandleShape (liftToSymbolic x) b i n
liftToSymbolic (WordMapShape w m) = WordMapShape w (fmap liftToSymbolic m)

sameshape :: ShapeDom tp -> ShapeDom tp -> Bool
sameshape SymbolicShape SymbolicShape = True
sameshape ConcreteShape ConcreteShape = True
sameshape BotShape BotShape = True
sameshape (LitShape x) (LitShape y) = x == y
sameshape (ComplexShape r1 i1) (ComplexShape r2 i2) = sameshape r1 r2 && sameshape i1 i2
sameshape (MaybeShape b1 x) (MaybeShape b2 y) = b1 == b2 && sameshape x y
sameshape (StructShape xs) (StructShape ys) =
   and $ toListFC ignoreOut $ runIdentity $ Ctx.zipWithM (\x y -> return $ Ignore $ sameshape x y) xs ys
sameshape (IntShape w1 a) (IntShape w2 b) =
   case testEquality w1 w2 of
      Just Refl -> sameshape a b
      Nothing -> False
sameshape (UIntShape w1 a) (UIntShape w2 b) =
   case testEquality w1 w2 of
      Just Refl -> sameshape a b
      Nothing -> False
sameshape (MatlabHandleShape h1 b1 i1 n1) (MatlabHandleShape h2 b2 i2 n2)
  | i1 == i2 && b1 == b2 && n1 == n2 = sameshape h1 h2
sameshape (ArrayShape a1) (ArrayShape a2)
  | MDA.dim a1 == MDA.dim a2 = execState (MDA.zipWithM (\x y -> modify (\b -> b && sameshape x y)) a1 a2) True
sameshape (MatlabStructShape m1) (MatlabStructShape m2)
  | Map.keysSet m1 == Map.keysSet m2 = Map.foldr' (&&) True $ Map.intersectionWith sameshape m1 m2
sameshape (VectorShape v1) (VectorShape v2)
  | V.length v1 == V.length v2 = V.foldr' (&&) True $ V.zipWith sameshape v1 v2
sameshape (StringMapShape m1) (StringMapShape m2)
  | Map.keysSet m1 == Map.keysSet m2 = Map.foldr' (&&) True $ Map.intersectionWith sameshape m1 m2
sameshape (MatlabValueShape sw1) (MatlabValueShape sw2) =
  foldlF (\x (Ignore y) -> x && y) True $ zipSwitchWith (\x y -> Ignore (sameshape x y)) sw1 sw2
sameshape (WordMapShape w1 m1) (WordMapShape w2 m2)
  | Just Refl <- testEquality w1 w2 = Map.foldr (&&) True $
          Map.mergeWithKey (\_ a b -> Just $ sameshape a b) (fmap (const False)) (fmap (const False)) m1 m2

sameshape _ _ = False

instance Eq (ShapeDom tp) where
  x == y = sameshape x y


shapelub :: ShapeDom tp -> ShapeDom tp -> ShapeDom tp
shapelub SymbolicShape _ = SymbolicShape
shapelub _ SymbolicShape = SymbolicShape
shapelub BotShape y = y
shapelub x BotShape = x
shapelub ConcreteShape y = mapConcrete y ConcreteShape
shapelub x ConcreteShape = mapConcrete x ConcreteShape

shapelub (IntShape w1 a) (IntShape w2 b) =
  case testEquality w1 w2 of
    Just Refl -> IntShape w1 (shapelub a b)
    Nothing -> BotShape
shapelub (UIntShape w1 a) (UIntShape w2 b) =
  case testEquality w1 w2 of
    Just Refl -> UIntShape w1 (shapelub a b)
    Nothing -> BotShape
shapelub (ComplexShape r1 i1) (ComplexShape r2 i2) = ComplexShape (shapelub r1 r2) (shapelub i1 i2)
shapelub (MaybeShape b1 x) (MaybeShape b2 y) = MaybeShape (b1 || b2) (shapelub x y)
shapelub (StructShape xs) (StructShape ys) =
   StructShape $ runIdentity $ Ctx.zipWithM (\x y -> return $ shapelub x y) xs ys
shapelub (MatlabValueShape sw1) (MatlabValueShape sw2) = MatlabValueShape (zipSwitchWith shapelub sw1 sw2)
shapelub (MatlabHandleShape h1 b1 i1 n1) (MatlabHandleShape h2 b2 i2 n2)
  | i1 == i2 && b1 == b2 && n1 == n2 = MatlabHandleShape (shapelub h1 h2) b1 i1 n1
  | otherwise = mapConcrete (shapelub h1 h2) ConcreteShape
shapelub (LitShape x) (LitShape y)
  | x == y = LitShape x
  | otherwise = ConcreteShape
shapelub (ArrayShape a1) (ArrayShape a2)
  | MDA.dim a1 == MDA.dim a2 = ArrayShape (MDA.zipWith shapelub a1 a2)
  | otherwise = SymbolicShape
shapelub (MatlabStructShape m1) (MatlabStructShape m2)
  | Map.keysSet m1 == Map.keysSet m2 = MatlabStructShape (Map.intersectionWith shapelub m1 m2)
  | otherwise = SymbolicShape
shapelub (VectorShape v1) (VectorShape v2)
  | V.length v1 == V.length v2 = VectorShape (V.zipWith shapelub v1 v2)
  | otherwise = SymbolicShape
shapelub (StringMapShape m1) (StringMapShape m2)
  | Map.keysSet m1 == Map.keysSet m2 = StringMapShape (Map.intersectionWith shapelub m1 m2)
  | otherwise = SymbolicShape
shapelub (WordMapShape w1 m1) (WordMapShape _w2 m2)
  | Map.keysSet m1 == Map.keysSet m2 = WordMapShape w1 (Map.intersectionWith shapelub m1 m2)
  | otherwise = SymbolicShape

shapelub _ _ = error "impossible! unexpected shape combination!"



op1' :: (ShapeLit a -> ShapeDom b)
     -> ShapeDom a -> ShapeDom b
op1' _ BotShape = BotShape
op1' f (LitShape x) = f x
op1' _ ConcreteShape = ConcreteShape
op1' _ _ = SymbolicShape

op1 :: (Show (ShapeLit b), Eq (ShapeLit b))
    => (ShapeLit a -> ShapeLit b)
    -> ShapeDom a -> ShapeDom b
op1 f = op1' (LitShape . f)

op2' :: (ShapeLit a -> ShapeLit b -> ShapeDom c)
     -> ShapeDom a -> ShapeDom b -> ShapeDom c
op2' _ BotShape _ = BotShape
op2' _ _ BotShape = BotShape
op2' f (LitShape x) (LitShape y) = f x y
op2' _ ConcreteShape (LitShape _) = ConcreteShape
op2' _ (LitShape _) ConcreteShape = ConcreteShape
op2' _ ConcreteShape ConcreteShape = ConcreteShape
op2' _ _ _ = SymbolicShape

op2 :: (Show (ShapeLit c), Eq (ShapeLit c))
    => (ShapeLit a -> ShapeLit b -> ShapeLit c)
    -> ShapeDom a -> ShapeDom b -> ShapeDom c
op2 f = op2' (\x y -> LitShape (f x y))

intop1 :: (Show (ShapeLit c), Eq (ShapeLit c))
    => (Integer -> ShapeLit c)
    -> ShapeDom MatlabIntType
    -> ShapeDom c
intop1 f (IntShape w x) = op1 (f . toSigned w) x
intop1 _ x = mapConcrete x ConcreteShape

intop2 :: (Show (ShapeLit c), Eq (ShapeLit c))
    => (Integer -> Integer -> ShapeLit c)
    -> ShapeDom MatlabIntType
    -> ShapeDom MatlabIntType
    -> ShapeDom c
intop2 f (IntShape w1 x) (IntShape w2 y) =
  case testEquality w1 w2 of
    Just Refl -> op2 (\a b -> f (toSigned w1 a) (toSigned w1 b)) x y
    Nothing -> BotShape
intop2 _ x y = mapConcrete x (mapConcrete y ConcreteShape)

uintop1 :: (Show (ShapeLit c), Eq (ShapeLit c))
    => (Integer -> ShapeLit c)
    -> ShapeDom MatlabUIntType
    -> ShapeDom c
uintop1 f (UIntShape _ x) = op1 f x
uintop1 _ x = mapConcrete x ConcreteShape

uintop2 :: (Show (ShapeLit c), Eq (ShapeLit c))
    => (Integer -> Integer -> ShapeLit c)
    -> ShapeDom MatlabUIntType
    -> ShapeDom MatlabUIntType
    -> ShapeDom c
uintop2 f (UIntShape w1 x) (UIntShape w2 y) =
  case testEquality w1 w2 of
    Just Refl -> op2 f x y
    Nothing -> BotShape
uintop2 _ x y = mapConcrete x (mapConcrete y ConcreteShape)


arrayReplicateShape
   :: ShapeDom ArrayDimType
   -> ShapeDom (ArrayElts tp)
   -> ShapeDom tp
arrayReplicateShape BotShape _ = BotShape
arrayReplicateShape _ BotShape = BotShape
arrayReplicateShape (LitShape dim) y_sh = ArrayShape (MDA.replicate dim y_sh)
arrayReplicateShape ConcreteShape y_sh = mapConcrete y_sh ConcreteShape
arrayReplicateShape _ _ = SymbolicShape

arrayDimShape
   :: ShapeDom tp
   -> ShapeDom ArrayDimType
arrayDimShape BotShape = BotShape
arrayDimShape (ArrayShape a) = LitShape (MDA.dim a)
arrayDimShape ConcreteShape  = ConcreteShape
arrayDimShape _ = SymbolicShape

arrayResizeShape
   :: ShapeDom tp
   -> ShapeDom ArrayDimType
   -> ShapeDom (ArrayElts tp)
   -> ShapeDom tp
arrayResizeShape BotShape _ _ = BotShape
arrayResizeShape _ BotShape _ = BotShape
arrayResizeShape _ _ BotShape = BotShape
arrayResizeShape ConcreteShape y z = mapConcrete y (mapConcrete z ConcreteShape)
arrayResizeShape (ArrayShape a) (LitShape dim) z =
    ArrayShape $ MDA.generate dim (\i -> fromMaybe z (a MDA.!? i))
arrayResizeShape _ _ _ = SymbolicShape

asLit :: ShapeDom tp -> Maybe (ShapeLit tp)
asLit (LitShape x) = Just x
asLit _ = Nothing

arrayLookupShape
   :: ShapeDom tp
   -> ShapeDom (VectorType NatType)
   -> ShapeDom (ArrayElts tp)
arrayLookupShape BotShape _ = BotShape
arrayLookupShape _ BotShape = BotShape
arrayLookupShape ConcreteShape i = mapConcrete i ConcreteShape
arrayLookupShape (ArrayShape a) ConcreteShape = foldl shapelub BotShape a
arrayLookupShape (ArrayShape a) (VectorShape n)
  | Just i <- traverse asLit n =
     case a MDA.!? (MDA.indexFromVector i) of
       Just r  -> r
       Nothing -> SymbolicShape
arrayLookupShape _ _ = SymbolicShape

arrayAsSingletonShape
   :: ShapeDom tp
   -> ShapeDom (MaybeType (ArrayElts tp))
arrayAsSingletonShape BotShape = BotShape
arrayAsSingletonShape ConcreteShape = ConcreteShape
arrayAsSingletonShape (ArrayShape sh) =
  case MDA.asSingleton sh of
    Just x  -> MaybeShape False x
    Nothing -> MaybeShape True  BotShape
arrayAsSingletonShape _ = SymbolicShape


indexArrayShape
   :: ShapeDom tp
   -> ShapeDom MultiDimArrayIndexType
   -> ShapeDom tp
indexArrayShape BotShape _ = BotShape
indexArrayShape _ BotShape = BotShape
indexArrayShape a ConcreteShape = mapConcrete a ConcreteShape
indexArrayShape (ArrayShape sh) (ArrayShape ish) =
  let shlub = foldr shapelub BotShape sh
      idx (VectorShape _) = shlub -- FIXME, lookup the actual shape
      idx s = mapConcrete s shlub
   in ArrayShape $ MDA.map idx ish
indexArrayShape a (ArrayShape ish) =
   ArrayShape $ MDA.map (\_ -> mapConcrete a ConcreteShape) ish
indexArrayShape _ _ = SymbolicShape

arrayEntryShape
   :: ShapeDom tp
   -> ShapeDom MultiDimArrayIndexType
   -> ShapeDom (ArrayElts tp)
arrayEntryShape BotShape _ = BotShape
arrayEntryShape _ BotShape = BotShape
arrayEntryShape (ArrayShape sh) (ArrayShape ish) =
   case MDA.asSingleton ish of
     Just (VectorShape v) ->
       case traverse (\i -> case i of LitShape x -> Just (fromIntegral x); _ -> Nothing) v of
         Just v' -> fromMaybe BotShape (sh MDA.!? (MDA.indexFromVector v'))
         Nothing -> mapConcrete (VectorShape v) (foldl shapelub BotShape sh)
     Just i -> mapConcrete i (foldl shapelub BotShape sh)
     Nothing -> BotShape
arrayEntryShape (ArrayShape sh) i = mapConcrete i (foldl shapelub BotShape sh)
arrayEntryShape a i = mapConcrete a (mapConcrete i ConcreteShape)

arrayEqShape
   :: (ShapeDom (ArrayElts tp) -> ShapeDom (ArrayElts tp) -> ShapeDom BoolType)
   -> ShapeDom tp
   -> ShapeDom tp
   -> ShapeDom BoolType
arrayEqShape f (ArrayShape sha) (ArrayShape shb)
  | MDA.dim sha == MDA.dim shb = foldl (op2 (&&)) (LitShape True) $ MDA.zipWith f sha shb
  | otherwise = LitShape False
arrayEqShape _ a b = mapConcrete a (mapConcrete b ConcreteShape)

mapArrayShape
   :: (ShapeDom (ArrayElts a) -> ShapeDom (ArrayElts b))
   -> ShapeDom a
   -> ShapeDom b
mapArrayShape _ BotShape = BotShape
mapArrayShape _ ConcreteShape = ConcreteShape
mapArrayShape f (ArrayShape a) = ArrayShape $ MDA.map f a
mapArrayShape _ _ = SymbolicShape


computeArraySeq :: Rational -> Rational -> Rational -> ShapeDom CplxArrayType
computeArraySeq l idx u
  | idx == 0         = ArrayShape MDA.empty
  | idx > 0 && l > u = ArrayShape MDA.empty
  | idx < 0 && l < u = ArrayShape MDA.empty
  | otherwise =
       let result_len :: Integer
           result_len = 1 + floor ((u - l) / idx)
           cvals = V.unfoldrN (fromInteger result_len) (\r -> Just (r,r+idx)) l
        in ArrayShape $ MDA.rowVector $ V.map (\r -> ComplexShape (LitShape r) (LitShape 0)) $ cvals

botSwitch :: MSwitch ShapeDom
botSwitch = constMSwitch BotShape

reg_shape :: forall ctx tp. Reg ctx tp -> Assignment ShapeDom ctx -> ShapeDom tp
reg_shape reg asgn = asgn Ctx.! (regIndex reg)

shape_expr :: forall ctx tp. Expr ctx tp -> Assignment ShapeDom ctx -> ShapeDom tp
shape_expr (App app) asgn =
  let f :: forall tp'. Reg ctx tp' -> ShapeDom tp'
      f x = reg_shape x asgn
   in case app of
       EmptyApp -> ConcreteShape

       BoolLit b -> LitShape b
       Not x -> op1 not (f x)
       And x y -> op2 (&&) (f x) (f y)
       Or x y -> op2 (||) (f x) (f y)
       BoolXor x y -> op2 xor (f x) (f y)
       BoolIte b x y ->
         case f b of
           LitShape True  -> f x
           LitShape False -> f y
           fb -> mapConcrete fb $ shapelub (f x) (f y)

       NatLit n -> LitShape n
       NatEq x y -> op2 (==) (f x) (f y)
       NatLt x y -> op2 (<) (f x) (f y)
       NatLe x y -> op2 (<=) (f x) (f y)
       NatAdd x y -> op2 (+) (f x) (f y)
       NatSub x y -> op2 (-) (f x) (f y)
       NatMul x y -> op2 (*) (f x) (f y)
       NatToInteger x -> op1 fromIntegral (f x)

       IntLit x -> LitShape x
       IntAdd x y -> op2 (+) (f x) (f y)
       IntSub x y -> op2 (-) (f x) (f y)
       IntMul x y -> op2 (*) (f x) (f y)
       IntEq x y -> op2 (==) (f x) (f y)
       IntLt x y -> op2 (<) (f x) (f y)
       IntegerToReal x -> op1 fromIntegral (f x)

       JustValue _ x  -> MaybeShape False (f x)
       NothingValue _ -> MaybeShape True  BotShape

       ----------------------------------------------------------------------
       -- MultiDimArray

       ArrayEmpty _ -> ArrayShape MDA.empty
       ArrayReplicate _ x y -> arrayReplicateShape (f x) (f y)
       ArrayDim x -> arrayDimShape (f x)
       ArrayResize _ x y z -> arrayResizeShape (f x) (f y) (f z)
       ArrayLookup _ a i -> arrayLookupShape (f a) (f i)
       ArrayAsSingleton _ a -> arrayAsSingletonShape (f a)
       IndexArray _ a i -> indexArrayShape (f a) (f i)
       -- ArrayEntry _ a i -> arrayEntryShape (f a) (f i)

       ArrayProduct _ v ->
          let v' = V.map f v in
          case traverse (\i -> case i of ArrayShape a -> Just a; _ -> Nothing) v' of
             Nothing -> V.foldr mapConcrete ConcreteShape v'
             Just v'' -> ArrayShape
                       . MDA.map (VectorShape . V.fromList)
                       . MDA.arrayProduct
                       $ V.toList v''

       VectorLit _ v -> VectorShape $ V.map f v
       VectorReplicate _ n x ->
         case (f n, f x) of
           (LitShape n', sh_x) -> VectorShape $ V.replicate (fromIntegral n') sh_x
           (fn, fx) -> mapConcrete fn (mapConcrete fx ConcreteShape)

       VectorIsEmpty x ->
          case f x of
            VectorShape v -> LitShape (V.length v == 0)
            fx -> mapConcrete fx ConcreteShape

       VectorSize x ->
          case f x of
            VectorShape v -> LitShape $ fromIntegral (V.length v)
            fx -> mapConcrete fx ConcreteShape

       VectorGetEntry _ v n ->
         case (f v, f n) of
           (VectorShape sh, LitShape n') -> sh V.! (fromIntegral n')
           (VectorShape sh, fn) -> mapConcrete fn (V.foldl shapelub BotShape sh)
           (fv, fn) -> mapConcrete fv (mapConcrete fn ConcreteShape)

       VectorSetEntry _ v n x ->
         case (f v, f n, f x) of
           (VectorShape sh, LitShape n', x_sh) ->
             VectorShape $ sh V.// [(fromIntegral n', x_sh)]
           (VectorShape sh, fn, x_sh) ->
             mapConcrete fn (VectorShape $ V.map (shapelub x_sh) sh)
           (fv, fn, fx) -> mapConcrete fv (mapConcrete fn (mapConcrete fx ConcreteShape))

       HandleLit h -> LitShape h
       Closure _ _ h _ x -> mapConcrete (f h) (mapConcrete (f x) ConcreteShape)

       EnumTo x ->
         case f x of
           LitShape n -> ArrayShape (MDA.rowVector
                (V.generate (fromIntegral n) (\i -> LitShape (succ (fromIntegral i)))))
           fx -> mapConcrete fx ConcreteShape

       RationalLit d -> LitShape d
       RealAdd x y -> op2 (+) (f x) (f y)
       RealSub x y -> op2 (-) (f x) (f y)
       RealMul x y -> op2 (*) (f x) (f y)
       RealEq x y -> op2 (==) (f x) (f y)
       RealLt x y -> op2 (<) (f x) (f y)
       RealIsInteger x -> op1 (\r -> numerator r == 1) (f x)
       RealIte b x y ->
         case f b of
           LitShape True  -> f x
           LitShape False -> f y
           fb -> mapConcrete fb $ shapelub (f x) (f y)
       RealToNat x ->
         case f x of
           LitShape rat ->
               if rat >= 0 && denominator rat == 1
                   then LitShape (fromIntegral (numerator rat))
                   else BotShape
           fx -> mapConcrete fx ConcreteShape

       Complex x y -> ComplexShape (f x) (f y)

       RealPart x ->
          case f x of
            (ComplexShape r _) -> r
            fx -> mapConcrete fx ConcreteShape

       ImagPart x ->
          case f x of
            (ComplexShape _ i) -> i
            fx -> mapConcrete fx ConcreteShape

       MatlabCharLit c -> LitShape c
       MatlabCharEq x y -> op2 (==) (f x) (f y)
       MatlabCharToNat x -> op1 (fromIntegral . fromEnum) (f x)

       CplxArrayEq a1 a2 ->
           let eqcplx :: ShapeDom ComplexRealType
                      -> ShapeDom ComplexRealType
                      -> ShapeDom BoolType
               eqcplx BotShape _ = BotShape
               eqcplx _ BotShape = BotShape
               eqcplx ConcreteShape x = mapConcrete x ConcreteShape
               eqcplx x ConcreteShape = mapConcrete x ConcreteShape
               eqcplx (ComplexShape r1 i1) (ComplexShape r2 i2) =
                   op2 (&&) (op2 (==) r1 r2 :: ShapeDom BoolType)
                            (op2 (==) i1 i2 :: ShapeDom BoolType)
               eqcplx _ _ = SymbolicShape
            in arrayEqShape eqcplx (f a1) (f a2)

       CplxArrayIsReal x ->
          case f x of
            BotShape -> BotShape
            ConcreteShape -> ConcreteShape
            ArrayShape sh ->
              let g :: ShapeDom BoolType
                    -> ShapeDom ComplexRealType
                    -> ShapeDom BoolType
                  g (LitShape b) (ComplexShape r (LitShape i)) =
                    let r' = mapConcrete r ConcreteShape in
                    if r' == ConcreteShape
                       then LitShape (b && i == 0)
                       else r'
                  g s s' = shapelub s (mapConcrete s' ConcreteShape)
              in foldl g (LitShape True) sh
            _ -> SymbolicShape

       IntArrayToCplxArray a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       UIntArrayToCplxArray a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       LogicArrayToCplxArray a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       CharArrayToCplxArray a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)

       -- FIXME? calculate the indices in the known case?
       CplxArrayAsPosNat x -> mapConcrete (f x) ConcreteShape

       BVLit w x -> LitShape $ toUnsigned w x
       BVUndef _ -> SymbolicShape  -- FIXME?
       BVConcat _w1 w2 x y -> op2 (\a b ->
                                    (a `shiftL` (fromIntegral (natValue w2))) .|. b)
                                  (f x) (f y)
       BVSelect idx n _ x ->
         op1 (\a -> toUnsigned n (a `shiftR` (fromIntegral (natValue idx)))) (f x)
       BVTrunc w' _ x -> op1 (toUnsigned w') (f x)
       BVZext _ _ x -> op1 id (f x)
       BVSext w' w x ->
         op1 (toUnsigned w' . toSigned w) (f x)
       BVEq _ x y   -> op2 (\a b -> a == b) (f x) (f y)
       BVNot _ x    -> op1 (\a -> if a == 0 then 1 else 0) (f x)
       BVAdd w x y  -> op2 (\a b -> toUnsigned w $ a + b) (f x) (f y)
       BVSub w x y  -> op2 (\a b -> toUnsigned w $ a + b) (f x) (f y)
       BVMul w x y  -> op2 (\a b -> toUnsigned w $ a * b) (f x) (f y)
       BVUdiv _ x y -> op2 (\a b -> a `div` b) (f x) (f y)
       BVUrem _ x y -> op2 (\a b -> a `rem` b) (f x) (f y)
       BVSdiv w x y -> op2 (\a b ->
                             toUnsigned w $ (toSigned w a) `div` (toSigned w b))
                           (f x) (f y)
       BVSrem w x y -> op2 (\a b ->
                             toUnsigned w $ (toSigned w a) `rem` (toSigned w b))
                           (f x) (f y)
       BVUlt _ x y  -> op2 (\a b -> a < b) (f x) (f y)
       BVUle _ x y  -> op2 (\a b -> a <= b) (f x) (f y)
       BVSlt w x y  -> op2 (\a b -> toSigned w a < toSigned w b) (f x) (f y)
       BVSle w x y  -> op2 (\a b -> toSigned w a <= toSigned w b) (f x) (f y)
       BVCarry w x y -> op2 (\a b -> a + b >= 2^(widthVal w)) (f x) (f y)
       BVSCarry w x y -> op2 (\a b -> let n = toSigned w a + toSigned w b
                                       in n /= toUnsigned w n)
                             (f x) (f y)
       BVSBorrow w x y -> op2 (\a b -> let n = toSigned w a - toSigned w b
                                        in n /= toUnsigned w n)
                              (f x) (f y)
       BVShl _ x y  -> op2 (\a b -> a `shiftL` (fromIntegral b)) (f x) (f y)
       BVLshr _ x y -> op2 (\a b -> a `shiftR` (fromIntegral b)) (f x) (f y)
       BVAshr w x y -> op2 (\a b ->
                             toUnsigned w $ (toSigned w a) `shiftR` (fromIntegral b))
                           (f x) (f y)
       BVAnd _ x y  -> op2 (\a b -> a .&. b) (f x) (f y)
       BVOr _ x y   -> op2 (\a b -> a .|. b) (f x) (f y)
       BVXor _ x y  -> op2 (\a b -> a `xor` b) (f x) (f y)
       BVNonzero _ x -> op1 (\a -> a /= 0) (f x)
       BoolToBV _w x -> op1 (\a -> if a then 1 else 0) (f x)
       BvToNat _ x -> op1 fromInteger (f x)
       BVIte b _w x y ->
         case f b of
           LitShape True  -> f x
           LitShape False -> f y
           fb -> mapConcrete fb $ shapelub (f x) (f y)

       MkStruct _ xs -> StructShape $ fmapFC f xs
       GetStruct x idx _ ->
          case f x of
            StructShape xs -> xs Ctx.! idx
            x' -> mapConcrete x' ConcreteShape
       SetStruct _ x idx y ->
          case f x of
            StructShape xs -> StructShape $ Ctx.update idx (f y) xs
            x' -> mapConcrete x' (mapConcrete (f y) ConcreteShape)

       EmptyWordMap w _tp -> WordMapShape w Map.empty
       InsertWordMap w _tp idx val wm ->
          case (f idx, f wm) of
             (LitShape idxLit, WordMapShape _ m) ->
               WordMapShape w (Map.insert idxLit (f val) m)
             (idxShape, wmShape) ->
                 mapConcrete idxShape
               . mapConcrete (f val)
               $ mapConcrete wmShape ConcreteShape
       LookupWordMap _tp idx wm ->
          case (f idx, f wm) of
             (LitShape idxLit, WordMapShape _w m) ->
               fromMaybe SymbolicShape (Map.lookup idxLit m)
             (idxShape, wmShape) ->
               mapConcrete idxShape (mapConcrete wmShape ConcreteShape)
       LookupWordMapWithDefault _tp idx wm def ->
          case (f idx, f wm) of
             (LitShape idxLit, WordMapShape _w m) ->
               fromMaybe (f def) (Map.lookup idxLit m)
             (idxShape, wmShape) ->
                 mapConcrete (f def)
               . mapConcrete idxShape
               $ mapConcrete wmShape ConcreteShape

       MatlabIntLit w x -> IntShape w $ LitShape x
       MatlabIntEq x y -> intop2 (\m n -> m == n) (f x) (f y)
       MatlabIntLt x y -> intop2 (\m n -> m < n) (f x) (f y)
       MatlabIntIsPos x -> intop1 (\n -> n > 0) (f x)
       MatlabIntToNat x -> intop1 (\n -> fromIntegral n) (f x)

       IntArrayWidth a -> mapConcrete (f a) ConcreteShape
       MatlabIntArrayEmpty x -> mapConcrete (f x) (ArrayShape MDA.empty)
       MatlabIntArraySingleton x -> ArrayShape $ MDA.singleton (f x)
       MatlabIntArrayDim a -> arrayDimShape (f a)
       MatlabIntArrayResize x y -> arrayResizeShape (f x) (f y) ConcreteShape
       MatlabIntArrayLookup a i -> arrayLookupShape (f a) (f i)
       MatlabIntArrayAsSingleton a -> arrayAsSingletonShape (f a)
       MatlabIntArrayIndex a i -> indexArrayShape (f a) (f i)
       MatlabIntArrayEq a b -> arrayEqShape (intop2 (\m n -> m == n)) (f a) (f b)
       MatlabIntArrayAsPosNat x -> mapConcrete (f x) ConcreteShape --FIXME? calculate the indices in the known case?
       CplxArrayToMatlabInt a w -> mapConcrete (f w) $ mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       MatlabIntArraySetWidth a w -> mapConcrete (f w) $ mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       MatlabUIntArrayToInt a w -> mapConcrete (f w) $ mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       LogicArrayToMatlabInt a w -> mapConcrete (f w) $ mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       CharArrayToMatlabInt a w -> mapConcrete (f w) $ mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)

       MatlabUIntLit w x -> UIntShape w $ LitShape x
       MatlabUIntEq x y -> uintop2 (\m n -> m == n) (f x) (f y)
       MatlabUIntLt x y -> uintop2 (\m n -> m < n) (f x) (f y)
       MatlabUIntIsPos x -> uintop1 (\n -> n > 0) (f x)
       MatlabUIntToNat x -> uintop1 (\n -> fromIntegral n) (f x)

       UIntArrayWidth x -> mapConcrete (f x) ConcreteShape
       MatlabUIntArrayEmpty x -> mapConcrete (f x) (ArrayShape MDA.empty)
       MatlabUIntArraySingleton x -> ArrayShape $ MDA.singleton (f x)
       MatlabUIntArrayDim a -> arrayDimShape (f a)
       MatlabUIntArrayResize x y -> arrayResizeShape (f x) (f y) ConcreteShape
       MatlabUIntArrayLookup a i -> arrayLookupShape (f a) (f i)
       MatlabUIntArrayAsSingleton a -> arrayAsSingletonShape (f a)
       MatlabUIntArrayIndex a i -> indexArrayShape (f a) (f i)
       MatlabUIntArrayEq x y -> arrayEqShape (uintop2 (\m n -> m == n)) (f x) (f y)
       MatlabUIntArrayAsPosNat x -> mapConcrete (f x) ConcreteShape

       CplxArrayToMatlabUInt a w ->
           mapConcrete (f w)
         . mapArrayShape (\x -> mapConcrete x ConcreteShape)
         $ f a
       MatlabIntArrayToUInt a w ->
           mapConcrete (f w)
         . mapArrayShape (\x -> mapConcrete x ConcreteShape)
         $ f a
       MatlabUIntArraySetWidth a w ->
           mapConcrete (f w)
         . mapArrayShape (\x -> mapConcrete x ConcreteShape)
         $ f a
       LogicArrayToMatlabUInt a w ->
           mapConcrete (f w)
         . mapArrayShape (\x -> mapConcrete x ConcreteShape)
         $ f a
       CharArrayToMatlabUInt a w ->
           mapConcrete (f w)
         . mapArrayShape (\x -> mapConcrete x ConcreteShape)
         $ f a

       LogicArrayEq x y -> arrayEqShape (op2 (==)) (f x) (f y)
       LogicArrayToIndices a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       CplxArrayToLogic a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       MatlabIntArrayToLogic a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       MatlabUIntArrayToLogic a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)

       AllEntriesAreTrue a -> mapConcrete (f a) ConcreteShape

       CharVectorLit cv -> ArrayShape
                         . MDA.rowVector
                         . V.map (LitShape . toEnum . fromIntegral)
                         $ CV.toVector cv

       CharArrayEq x y -> arrayEqShape (op2 (==)) (f x) (f y)
       CplxArrayToChar a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)
       CharArrayAsPosNat a -> mapConcrete (f a) ConcreteShape
       CharArrayToLogic a -> mapArrayShape (\x -> mapConcrete x ConcreteShape) (f a)

       UpdateCellEntry x y z -> mapConcrete (f x) (mapConcrete (f y) (mapConcrete (f z) ConcreteShape))

       GetVarArgs x n ->
         case f x of
           VectorShape v -> ArrayShape $ MDA.rowVector $ V.drop (fromIntegral n) v
           fx -> mapConcrete fx ConcreteShape

       EmptyStructFields -> ConcreteShape
       FieldsEq x y -> mapConcrete (f x) (mapConcrete (f y) ConcreteShape)
       HasField x y -> mapConcrete (f x) (mapConcrete (f y) ConcreteShape)

       CplxArrayToMatlab x       -> MatlabValueShape botSwitch{ matchRealArray = f x }
       MatlabIntArrayToMatlab x  -> MatlabValueShape botSwitch{ matchIntArray = f x }
       MatlabUIntArrayToMatlab x -> MatlabValueShape botSwitch{ matchUIntArray = f x }
       LogicArrayToMatlab x      -> MatlabValueShape botSwitch{ matchLogicArray = f x }
       CharArrayToMatlab x       -> MatlabValueShape botSwitch{ matchCharArray = f x }
       CellArrayToMatlab x       -> MatlabValueShape botSwitch{ matchCellArray = f x }
       MatlabStructArrayToMatlab x -> MatlabValueShape botSwitch{ matchStructArray = f x }
       MatlabObjectArrayToMatlab x -> MatlabValueShape botSwitch{ matchObjectArray = f x }
       HandleToMatlab x          -> MatlabValueShape botSwitch{ matchHandle = f x }

       EmptyStringMap _ -> StringMapShape $ Map.empty
       InsertStringMapEntry _ mp nm v ->
         case (f mp, f nm, f v) of
           (StringMapShape sh_mp, LitShape nm_sh, v_sh) ->
             StringMapShape $ Map.insert nm_sh v_sh sh_mp
           (mp_sh, nm_sh, v_sh) ->
             mapConcrete mp_sh (mapConcrete nm_sh (mapConcrete v_sh ConcreteShape))

       TextLit l -> LitShape l
       AssignmentText l v -> mapConcrete (f l) (mapConcrete (f v) ConcreteShape)
       _ -> error "unmatched case in shape analysis"

shape_call :: CtxRepr args
           -> TypeRepr ret
           -> Reg ctx (FunctionHandleType args ret)
           -> ShapeDom (FunctionHandleType args ret)
           -> Assignment ShapeDom args
           -> ShapeDom ret
shape_call _ _ ex sh asgn = Debug.trace ("analysis encountered call: " ++ show (pretty ex) ++ " " ++ show sh) $
  case sh of
    _ -> mapConcrete sh (mapAsgnConcrete asgn ConcreteShape)
{-
    GlobalMatlabHandleShape' fn
      | fn == functionNameFromText (Text.pack "symbolic") -> symbolic_call asgn
      | fn == functionNameFromText (Text.pack "plus") -> plus_call asgn
      | fn == functionNameFromText (Text.pack "lt") -> cmp_call asgn
      | fn == functionNameFromText (Text.pack "equal") -> cmp_call asgn
      | fn == functionNameFromText (Text.pack "uint8") -> uint_call asgn
-}

{-
uint_call :: Assignment ShapeDom MatlabFunctionBaseArgs
          -> ShapeDom MatlabFunctionReturnType
uint_call asgn =
  case asgn Ctx.! (regIndex fnArgsReg) of
    VectorShape v
       | V.length v == 1 ->
           let xsh = v V.! 0
               xsh' = case xsh of
                        MatlabValueShape sw ->
                           (shapelub (mapArrayShape (\x -> mapConcrete x ConcreteShape) (matchRealArray sw))
                           (shapelub (mapArrayShape (\x -> mapConcrete x ConcreteShape) (matchIntArray sw))
                           (matchUIntArray sw)))
                        _ -> mapConcrete xsh ConcreteShape
           in VectorShape $ V.fromList [MaybeShape False $ MatlabValueShape botSwitch{ matchUIntArray = xsh' }]
       | otherwise -> BotShape
    sh -> VectorShape $ V.fromList
             [MaybeShape False $ MatlabValueShape botSwitch{ matchUIntArray = mapConcrete sh ConcreteShape }]

cmp_call :: Assignment ShapeDom MatlabFunctionBaseArgs
          -> ShapeDom MatlabFunctionReturnType
cmp_call asgn =
  case asgn Ctx.! (regIndex fnArgsReg) of
    VectorShape v
       | V.length v == 2 ->
           let xsh = v V.! 0
               ysh = v V.! 1
           in VectorShape $ V.fromList [MaybeShape False $ mapConcrete (shapelub xsh ysh) ConcreteShape]
       | otherwise -> BotShape
    sh -> mapConcrete sh ConcreteShape

plus_call :: Assignment ShapeDom MatlabFunctionBaseArgs
          -> ShapeDom MatlabFunctionReturnType
plus_call asgn =
  case asgn Ctx.! (regIndex fnArgsReg) of
    VectorShape v
       | V.length v == 2 ->
           let xsh = v V.! 0
               ysh = v V.! 1
           in VectorShape $ V.fromList [MaybeShape False (shapelub xsh ysh)]
       | otherwise -> BotShape
    sh -> mapConcrete sh ConcreteShape
-}

symbolic_call :: Assignment ShapeDom MatlabFunctionBaseArgs
              -> ShapeDom MatlabFunctionReturnType
symbolic_call _ = VectorShape $ V.fromList [MaybeShape True $ MatlabValueShape v]
 where v = MSwitch
           { matchRealArray   = SymbolicShape
           , matchIntArray    = SymbolicShape
           , matchUIntArray   = SymbolicShape
           , matchLogicArray  = SymbolicShape
           , matchCharArray   = BotShape
           , matchCellArray   = BotShape
           , matchStructArray = BotShape
           , matchHandle      = BotShape
           , matchSymLogicArray = BotShape
           , matchSymRealArray = BotShape
           , matchSymCplxArray = BotShape
           , matchSymIntArray  = BotShape
           , matchSymUIntArray = BotShape
           , matchObjectArray  = BotShape
           }

-- FIXME! do something better regarding function calls...
{-
shape_call _ _ (App (MatlabFunctionHandle (App (GlobalMatlabFunction fn)))) _ asgn
   | fn == functionNameFromText (Text.pack "symbolic") = VectorShape $ V.fromList [MaybeShape True SymbolicShape]
   | fn == functionNameFromText (Text.pack "plus") =
               VectorShape $ V.fromList [MaybeShape True (if allConcrete asgn then ConcreteShape else SymbolicShape)]
   | fn == functionNameFromText (Text.pack "uint8") =
               VectorShape $ V.fromList [MaybeShape True (if allConcrete asgn then ConcreteShape else SymbolicShape)]
   | allConcrete asgn = ConcreteShape
   | otherwise = SymbolicShape
shape_call _ _ ex sh _ = Debug.trace ("analysis encountered call: " ++ show (pretty ex) ++ show sh) $ SymbolicShape
-}

mapAsgnConcrete  :: Assignment ShapeDom args -> ShapeDom tp -> ShapeDom tp
mapAsgnConcrete asgn s0 = foldrFC mapConcrete s0 asgn


shapeAnalysis :: KildallForward blocks ShapeDom SymDom
shapeAnalysis =
  KildallForward
  { kfwd_lub   = shapelub
  , kfwd_bot   = BotShape
  , kfwd_club  = symlub
  , kfwd_cbot  = Dead
  , kfwd_same  = sameshape
  , kfwd_csame = (==)
  , kfwd_br    = \ex sh c -> case sh of
                               BotShape -> (Dead, Dead)
                               LitShape True  -> (c, Dead)
                               LitShape False -> (Dead, c)
                               ConcreteShape -> (c, c)
                               _ -> Debug.trace ("symbolic br: " ++ show (pretty ex)) (Symbolic, Symbolic)
  , kfwd_maybe = \_ ex sh c -> case sh of
                                 BotShape -> (Dead, BotShape, Dead)
                                 ConcreteShape -> (c, ConcreteShape, c)
                                 MaybeShape b a  -> let cjust = if a == BotShape then Dead else c
                                                        cnothing = if b then c else Dead
                                                     in (cjust, a, cnothing)
                                 _ -> Debug.trace ("symbolic maybe: "++show (pretty ex)) (Symbolic, SymbolicShape, Symbolic)
  , kfwd_mswitch = \ex sh c ->  case sh of
                                 BotShape ->
                                     let kp :: KildallPair ShapeDom SymDom tp
                                         kp = (KP BotShape Dead)
                                      in constMSwitch kp
                                 ConcreteShape ->
                                     let kp :: KildallPair ShapeDom SymDom tp
                                         kp = (KP ConcreteShape c)
                                      in constMSwitch kp
                                 MatlabValueShape sw ->
                                   fmapF (\a -> KP a (if a == BotShape then Dead else c)) sw
                                 _ -> Debug.trace ("symbolic switch: " ++ show (pretty ex)) $
                                     let kp :: KildallPair ShapeDom SymDom tp
                                         kp = (KP SymbolicShape Symbolic)
                                      in constMSwitch kp
  , kfwd_reg = \_ -> reg_shape
  , kfwd_expr = \_ -> shape_expr
  , kfwd_call = shape_call
  , kfwd_rdglobal = \gv -> Debug.trace (unwords ["analysis encountered global read:", show (globalName gv)])
                               $ SymbolicShape -- FIXME, pessimistic assumption: every global read is symbolic
  , kfwd_onentry = \_ (asgn,c) ->
         case c of
            -- If a given block is dead code, drag all value shapes down to the bottom element of the domain
            Dead -> (fmapFC (\_ -> BotShape) asgn, Dead)

            -- FIXME? dragging every shape up to SymbolicShape when symbolic control flow is encountered is pretty pessimistic.
            -- Can we do better?
            Symbolic -> (fmapFC liftToSymbolic asgn, Symbolic)

            _ -> (asgn, c)
  }


-- Force ShapeDom to be in context for next slice.
$(return [])

instance Show (ShapeDom tp) where
  showsPrec = $(structuralShowsPrec [t|ShapeDom|])

instance ShowF ShapeDom where
  showF = show


matlabShapeInit :: Ctx.Assignment ShapeDom MatlabFunctionBaseArgs
matlabShapeInit =
       (Ctx.extend (Ctx.extend (Ctx.extend (Ctx.extend Ctx.empty
                  (VectorShape $ V.fromList [bvshape, bvshape]))
                  ConcreteShape)
                  ConcreteShape)
                  ConcreteShape)

  where bvshape = MatlabValueShape
                   botSwitch{ matchIntArray =
                                  ArrayShape $ MDA.singleton $ IntShape (knownNat :: NatRepr 8) $ SymbolicShape
                            }
shapeResults
   :: Ctx.Assignment ShapeDom init
   -> CFG blocks init ret
   -> String
shapeResults begin cfg = unlines $
  (zipWith (\x y -> "%"++show x ++ " "++y) [(0::Integer)..] (toListFC (\ (KP a c) -> show (a,c)) asgn))
  ++
  [show (r, rc)]

 where (asgn, r, rc) = kildall_forward shapeAnalysis cfg (begin, Concrete)
