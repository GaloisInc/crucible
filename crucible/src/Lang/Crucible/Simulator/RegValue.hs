-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.RegValue
-- Description      : Runtime representation of CFG registers
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- RegValue is a type family that defines the runtime representation
-- of crucible types.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.RegValue
  ( RegValue
  , CanMux(..)
  , RegValue'(..)
  , VariantBranch(..)
  , MuxFn

    -- * Register values
  , AnyValue(..)
  , FnVal(..)
  , RolledType(..)
  , SomeInt(..)
  , SomeUInt(..)
  , SomeBVArray(..)
  , SomeSymbolicBVArray(..)

    -- * Value mux functions
  , ValMuxFn
  , eqMergeFn
  , mdaMuxFn
  , mergePartExpr
  , muxRecursive
  , muxStringMap
  , muxStruct
  , muxVariant
  , muxVector
  , muxHandle
  ) where

import           Control.Monad
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Proxy
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Word
import           GHC.TypeLits

import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.Utils.SymMultiDimArray as SMDA
import           Lang.MATLAB.MultiDimArray (MultiDimArray)
import qualified Lang.MATLAB.MultiDimArray as MDA

import           Lang.Crucible.FunctionHandle (FnHandle, handleName, RefCell)
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Types

type MuxFn p v = p -> v -> v -> IO v

-- | Maps register types to the associated value.
type family RegValue (sym :: *) (tp :: CrucibleType) :: * where
  RegValue sym (BaseToType bt) = SymExpr sym bt
  RegValue sym AnyType = AnyValue sym
  RegValue sym (ConcreteType a) = a
  RegValue sym UnitType = ()
  RegValue sym CharType = Word16
  RegValue sym StringType = Text
  RegValue sym (FunctionHandleType a r) = FnVal sym a r
  RegValue sym (MaybeType tp) = PartExpr (Pred sym) (RegValue sym tp)
  RegValue sym (VectorType tp) = V.Vector (RegValue sym tp)
  RegValue sym (StructType ctx) = Ctx.Assignment (RegValue' sym) ctx
  RegValue sym (VariantType ctx) = Ctx.Assignment (VariantBranch sym) ctx
  RegValue sym (ReferenceType a) = RefCell a
  RegValue sym (WordMapType w tp) = WordMap sym w tp
  RegValue sym IntWidthType = IntWidth
  RegValue sym UIntWidthType = UIntWidth
  RegValue sym (RecursiveType nm) = RolledType sym nm
  RegValue sym (IntrinsicType nm) = Intrinsic sym nm
  RegValue sym (MultiDimArrayType tp) = MultiDimArray (RegValue sym tp)
  RegValue sym (SymbolicMultiDimArrayType bt) = SMDA.SymMultiDimArray (SymExpr sym) bt
  RegValue sym MatlabIntType = SomeInt sym
  RegValue sym MatlabUIntType = SomeUInt sym
  RegValue sym MatlabIntArrayType = SomeBVArray (SymExpr sym)
  RegValue sym MatlabUIntArrayType = SomeBVArray (SymExpr sym)
  RegValue sym MatlabSymbolicIntArrayType = SomeSymbolicBVArray (SymExpr sym)
  RegValue sym MatlabSymbolicUIntArrayType = SomeSymbolicBVArray (SymExpr sym)
  RegValue sym (StringMapType tp) = Map Text (PartExpr (Pred sym) (RegValue sym tp))

-- | A newtype wrapper around RegValue.  This is wrapper necessary because
--   RegValue is a type family and, as such, cannot be partially applied.
newtype RegValue' sym tp = RV { unRV :: RegValue sym tp }

------------------------------------------------------------------------
-- FnVal

-- | Represents a function closure.
data FnVal (sym :: *) (args :: Ctx CrucibleType) (res :: CrucibleType) where
  ClosureFnVal :: !(FnVal sym (args ::> tp) ret)
               -> !(TypeRepr tp)
               -> !(RegValue sym tp)
               -> FnVal sym args ret

  HandleFnVal :: !(FnHandle a r) -> FnVal sym a r

closureFunctionName :: FnVal sym args res -> FunctionName
closureFunctionName (ClosureFnVal c _ _) = closureFunctionName c
closureFunctionName (HandleFnVal h) = handleName h

instance Show (FnVal sym a r) where
  show = show . closureFunctionName


-- | Version of muxfn specialized to CanMux.
type ValMuxFn sym tp = MuxFn (Pred sym) (RegValue sym tp)


------------------------------------------------------------------------
-- CanMux

class CanMux sym (tp :: CrucibleType) where
   muxReg :: sym
          -> p tp          -- ^ Unused type to identify what is being merged.
          -> ValMuxFn sym tp

-- | Merge function that checks if two values are equal, and
-- fails if they are not.
{-# INLINE eqMergeFn #-}
eqMergeFn :: Eq v => String -> MuxFn p v
eqMergeFn nm = \_ x y ->
  if x == y then
    return x
  else
    fail $ "Cannot merge dissimilar " ++ nm ++ "."

------------------------------------------------------------------------
-- RegValue AnyType instance

data AnyValue sym where
  AnyValue :: TypeRepr tp -> RegValue sym tp -> AnyValue sym

------------------------------------------------------------------------
-- RegValue () instance

instance CanMux sym UnitType where
  muxReg _ = \_ _ x _y -> return x

------------------------------------------------------------------------
-- RegValue instance for base types

instance IsBoolExprBuilder sym => CanMux sym BoolType where
  {-# INLINE muxReg #-}
  muxReg s = const $ itePred s

instance IsExprBuilder sym => CanMux sym NatType where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> natIte s

instance IsExprBuilder sym => CanMux sym IntegerType where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> intIte s

instance IsExprBuilder sym => CanMux sym RealValType where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> realIte s

instance IsExprBuilder sym => CanMux sym ComplexRealType where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> cplxIte s

------------------------------------------------------------------------
-- RegValue String instance

instance CanMux sym StringType where
  {-# INLINE muxReg #-}
  muxReg _ = \ _ -> eqMergeFn "strings"

------------------------------------------------------------------------
-- RegValue Vector instance

{-# INLINE muxVector #-}
muxVector :: MuxFn p e
          -> MuxFn p (V.Vector e)
muxVector f p x y
  | V.length x == V.length y = V.zipWithM (f p) x y
  | otherwise = fail "Cannot merge vectors with different dimensions."

instance CanMux sym tp => CanMux sym (VectorType tp) where
  {-# INLINE muxReg #-}
  muxReg s _ = muxVector (muxReg s (Proxy :: Proxy tp))

------------------------------------------------------------------------
-- RegValue WordMap instance

instance (IsExprBuilder sym, KnownNat w, KnownRepr BaseTypeRepr tp)
  => CanMux sym (WordMapType w tp) where
  {-# INLINE muxReg #-}
  muxReg s _ p = muxWordMap s knownNat knownRepr p

------------------------------------------------------------------------
-- RegValue MatlabChar instance


instance CanMux sym CharType where
  {-# INLINE muxReg #-}
  muxReg _ = \_ -> eqMergeFn "characters"

------------------------------------------------------------------------
-- RegValue IntWidth instance

instance CanMux sb IntWidthType where
  {-# INLINE muxReg #-}
  muxReg _ = \_ -> eqMergeFn "int width"

------------------------------------------------------------------------
-- RegValue UIntWidth instance

instance CanMux sym UIntWidthType where
  {-# INLINE muxReg #-}
  muxReg _ = \_ -> eqMergeFn "uint width"

------------------------------------------------------------------------
-- RegValue Maybe instance

mergePartExpr :: IsBoolExprBuilder sym
              => sym
              -> (Pred sym -> v -> v -> IO v)
              -> Pred sym
              -> PartExpr (Pred sym) v
              -> PartExpr (Pred sym) v
              -> IO (PartExpr (Pred sym) v)
mergePartExpr sym fn pt x y =
  case (x,y) of
    (PE px vx, PE py vy) -> do
      p' <- itePred sym pt px py
      v' <- fn pt vx vy
      return (PE p' v')
    (PE px vx, Unassigned) -> do
      p' <- andPred sym pt px
      return (PE p' vx)
    (Unassigned, PE py vy) -> do
      pf <- notPred sym pt
      p' <- andPred sym pf py
      return (PE p' vy)
    (Unassigned, Unassigned) ->
      return Unassigned

instance (IsBoolExprBuilder sym, CanMux sym tp) => CanMux sym (MaybeType tp) where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> do
    let f = muxReg s (Proxy :: Proxy tp)
     in mergePartExpr s f

------------------------------------------------------------------------
-- RegValue MultDimArray instance

{-# INLINE mdaMuxFn #-}
mdaMuxFn :: IsPred p => MuxFn p v -> MuxFn p (MultiDimArray v)
mdaMuxFn f p x y
  | Just b <- asConstantPred p = pure $! if b then x else y
  | MDA.dim x == MDA.dim y = MDA.zipWithM (f p) x y
  | otherwise = fail "Cannot merge arrays with different dimensions."

instance (IsExprBuilder sym, CanMux sym tp)
      => CanMux sym (MultiDimArrayType tp) where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> mdaMuxFn (muxReg s (Proxy :: Proxy tp))

data SomeSymbolicBVArray f where
  SomeSymbolicBVArray :: (1 <= w)
                      => NatRepr w
                      -> SMDA.SymMultiDimArray f (BaseBVType w)
                      -> SomeSymbolicBVArray f

instance IsExprBuilder sym => CanMux sym MatlabSymbolicIntArrayType where
  muxReg s _ c (SomeSymbolicBVArray wx x) (SomeSymbolicBVArray wy y)
    | Just Refl <- testEquality wx wy
      = SomeSymbolicBVArray wx <$> SMDA.muxArray s c x y
    | otherwise = fail $ unwords ["Cannot mux symbolic int arrays with different widths", show wx, show wy]


instance IsExprBuilder sym => CanMux sym MatlabSymbolicUIntArrayType where
  muxReg s _ c (SomeSymbolicBVArray wx x) (SomeSymbolicBVArray wy y)
    | Just Refl <- testEquality wx wy
      = SomeSymbolicBVArray wx <$> SMDA.muxArray s c x y
    | otherwise = fail $ unwords ["Cannot mux symbolic uint arrays with different widths", show wx, show wy]

------------------------------------------------------------------------
-- RegValue FunctionHandleType instance

-- TODO: Figure out how to actually compare these.
{-# INLINE muxHandle #-}
muxHandle :: IsPred (Pred sym)
          => sym
          -> Pred sym
          -> FnVal sym a r
          -> FnVal sym a r
          -> IO (FnVal sym a r)
muxHandle _ c x y
  | Just b <- asConstantPred c = pure $! if b then x else y
  | otherwise = return x


instance IsExprBuilder sym => CanMux sym (FunctionHandleType a r) where
  {-# INLINE muxReg #-}
  muxReg s = \_ c x y -> do
    muxHandle s c x y

------------------------------------------------------------------------
-- RegValue IdentValueMap instance

-- | Merge to string maps together.
{-# INLINE muxStringMap #-}
muxStringMap :: IsExprBuilder sym
             => sym
             -> MuxFn (Pred sym) e
             -> MuxFn (Pred sym) (Map Text (PartExpr (Pred sym) e))
muxStringMap sym = \f c x y -> do
  let keys = Set.toList $ Set.union (Map.keysSet x) (Map.keysSet y)
  fmap Map.fromList $ forM keys $ \k -> do
    let vx = joinMaybePE (Map.lookup k x)
    let vy = joinMaybePE (Map.lookup k y)
    r <- mergePartExpr sym f c vx vy
    return (k,r)

------------------------------------------------------------------------
-- RegValue Recursive instance

newtype RolledType sym nm = RolledType { unroll :: RegValue sym (UnrollType nm) }


{-# INLINE muxRecursive #-}
muxRecursive
   :: IsRecursiveType nm
   => (forall tp. TypeRepr tp -> ValMuxFn sym tp)
   -> SymbolRepr nm
   -> ValMuxFn sym (RecursiveType nm)
muxRecursive recf = \nm p x y -> do
   RolledType <$> recf (unrollType nm) p (unroll x) (unroll y)

------------------------------------------------------------------------
-- RegValue Struct instance

{-# INLINE muxStruct #-}
muxStruct
   :: (forall tp. TypeRepr tp -> ValMuxFn sym tp)
   -> CtxRepr ctx
   -> ValMuxFn sym (StructType ctx)
muxStruct recf ctx = \p x y ->
  Ctx.generateM (Ctx.size ctx) $ \i -> do
    RV <$> recf (ctx Ctx.! i) p (unRV $ x Ctx.! i) (unRV $ y Ctx.! i)

------------------------------------------------------------------------
-- RegValue Variant instance

newtype VariantBranch sym tp = VB { unVB :: PartExpr (Pred sym) (RegValue sym tp) }

{-# INLINE muxVariant #-}
muxVariant
   :: IsExprBuilder sym
   => sym
   -> (forall tp. TypeRepr tp -> ValMuxFn sym tp)
   -> CtxRepr ctx
   -> ValMuxFn sym (VariantType ctx)
muxVariant sym recf ctx = \p x y ->
  Ctx.generateM (Ctx.size ctx) $ \i ->
     VB <$> mergePartExpr sym
                (recf (ctx Ctx.! i))
                p
                (unVB (x Ctx.! i))
                (unVB (y Ctx.! i))


-------------------------
-- RegValue signed MatlabBV instance

data SomeInt sym where
  SomeInt :: (1 <= w) => NatRepr w -> SymBV sym w -> SomeInt sym

instance IsExprBuilder sym => CanMux sym MatlabIntType where
  {-# INLINE muxReg #-}
  muxReg s = \_ c (SomeInt w x) (SomeInt w' y) ->
       case testEquality w w' of
         Nothing -> fail "cannot merge MATAB ints of different widths"
         Just Refl -> SomeInt w <$> bvIte s c x y

-------------------------
-- RegValue unsigned MatlabBV instance

data SomeUInt sym where
  SomeUInt :: (1 <= w) => NatRepr w -> SymBV sym w -> SomeUInt sym

instance IsExprBuilder sym => CanMux sym MatlabUIntType where
  {-# INLINE muxReg #-}
  muxReg s = \_ c (SomeUInt w x) (SomeUInt w' y) ->
       case testEquality w w' of
         Nothing -> fail "cannot merge MATAB uints of different widths"
         Just Refl -> SomeUInt w <$> bvIte s c x y

------------------------------------------------------------------------
-- SomeBVArray

data SomeBVArray (v :: BaseType -> *) where
  SomeBVArray :: (1 <= n)
              => !(NatRepr n)
              -> !(MultiDimArray (v (BaseBVType n)))
              -> SomeBVArray v

instance MDA.HasDim (SomeBVArray val) where
   dim (SomeBVArray _ a) = MDA.dim a

--------------------
-- RegValue BV Array instances

instance IsExprBuilder sym => CanMux sym MatlabIntArrayType where
  {-# INLINE muxReg #-}
  muxReg s = \_ c (SomeBVArray w x) (SomeBVArray w' y) ->
    case testEquality w w' of
      Nothing -> fail "cannot merge MATAB int arrays of different widths"
      Just Refl -> SomeBVArray w <$> mdaMuxFn (bvIte s) c x y

instance IsExprBuilder sym => CanMux sym MatlabUIntArrayType where
  {-# INLINE muxReg #-}
  muxReg s = \_ c (SomeBVArray w x) (SomeBVArray w' y) ->
    case testEquality w w' of
      Nothing -> fail "cannot merge MATABu int arrays of different widths"
      Just Refl -> SomeBVArray w <$> mdaMuxFn (bvIte s) c x y
