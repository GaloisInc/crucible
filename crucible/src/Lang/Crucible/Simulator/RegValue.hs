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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Lang.Crucible.Simulator.RegValue
  ( RegValue
  , CanMux(..)
  , RegValue'(..)
  , VariantBranch(..)
  , injectVariant
  , MuxFn

    -- * Register values
  , AnyValue(..)
  , FnVal(..)
  , fnValType
  , RolledType(..)

    -- * Value mux functions
  , ValMuxFn
  , eqMergeFn
  , mergePartExpr
  , muxRecursive
  , muxStringMap
  , muxStruct
  , muxVariant
  , muxVector
  , muxHandle
  ) where

import           Control.Monad
import           Control.Monad.Trans.Class
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Proxy
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Word
import           GHC.TypeNats (KnownNat)

import qualified Data.Parameterized.Context as Ctx

import           What4.FunctionName
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Partial
import           What4.WordMap

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.MuxTree
import           Lang.Crucible.Backend

type MuxFn p v = p -> v -> v -> IO v

-- | Maps register types to the runtime representation.
type family RegValue (sym :: Type) (tp :: CrucibleType) :: Type where
  RegValue sym (BaseToType bt) = SymExpr sym bt
  RegValue sym (FloatType fi) = SymInterpretedFloat sym (CrucibleFloatMode sym) fi
  RegValue sym AnyType = AnyValue sym
  RegValue sym UnitType = ()
  RegValue sym CharType = Word16
  RegValue sym (FunctionHandleType a r) = FnVal sym a r
  RegValue sym (MaybeType tp) = PartExpr (Pred sym) (RegValue sym tp)
  RegValue sym (VectorType tp) = V.Vector (RegValue sym tp)
  RegValue sym (StructType ctx) = Ctx.Assignment (RegValue' sym) ctx
  RegValue sym (VariantType ctx) = Ctx.Assignment (VariantBranch sym) ctx
  RegValue sym (ReferenceType tp) = MuxTree sym (RefCell tp)
  RegValue sym (WordMapType w tp) = WordMap sym w tp
  RegValue sym (RecursiveType nm ctx) = RolledType sym nm ctx
  RegValue sym (IntrinsicType nm ctx) = Intrinsic sym nm ctx
  RegValue sym (StringMapType tp) = Map Text (PartExpr (Pred sym) (RegValue sym tp))

-- | A newtype wrapper around RegValue.  This is wrapper necessary because
--   RegValue is a type family and, as such, cannot be partially applied.
newtype RegValue' sym tp = RV { unRV :: RegValue sym tp }

------------------------------------------------------------------------
-- FnVal

-- | Represents a function closure.
data FnVal (sym :: Type) (args :: Ctx CrucibleType) (res :: CrucibleType) where
  ClosureFnVal ::
    !(FnVal sym (args ::> tp) ret) ->
    !(TypeRepr tp) ->
    !(RegValue sym tp) ->
    FnVal sym args ret

  VarargsFnVal ::
    !(FnHandle (args ::> VectorType AnyType) ret) ->
    !(CtxRepr addlArgs) ->
    FnVal sym (args <+> addlArgs) ret

  HandleFnVal ::
    !(FnHandle a r) ->
    FnVal sym a r


closureFunctionName :: FnVal sym args res -> FunctionName
closureFunctionName (ClosureFnVal c _ _) = closureFunctionName c
closureFunctionName (HandleFnVal h) = handleName h
closureFunctionName (VarargsFnVal h _) = handleName h

-- | Extract the runtime representation of the type of the given 'FnVal'
fnValType :: FnVal sym args res -> TypeRepr (FunctionHandleType args res)
fnValType (HandleFnVal h) = FunctionHandleRepr (handleArgTypes h) (handleReturnType h)
fnValType (VarargsFnVal h addlArgs) =
  case handleArgTypes h of
    args Ctx.:> _ -> FunctionHandleRepr (args Ctx.<++> addlArgs) (handleReturnType h)
fnValType (ClosureFnVal fn _ _) =
  case fnValType fn of
    FunctionHandleRepr allArgs r ->
      case allArgs of
        args Ctx.:> _ -> FunctionHandleRepr args r

instance Show (FnVal sym a r) where
  show = show . closureFunctionName

-- | Version of 'MuxFn' specialized to 'RegValue'
type ValMuxFn sym tp = MuxFn (Pred sym) (RegValue sym tp)

------------------------------------------------------------------------
-- CanMux

-- | A class for 'CrucibleType's that have a
--   mux function.
class CanMux sym (tp :: CrucibleType) where
   muxReg :: sym
          -> p tp          -- ^ Unused type to identify what is being merged.
          -> ValMuxFn sym tp

-- | Merge function that checks if two values are equal, and
-- fails if they are not.
{-# INLINE eqMergeFn #-}
eqMergeFn :: (IsSymInterface sym, Eq v) => sym -> String -> MuxFn p v
eqMergeFn sym nm = \_ x y ->
  if x == y then
    return x
  else
    addFailedAssertion sym
      $ Unsupported $ "Cannot merge dissimilar " ++ nm ++ "."

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

instance IsExprBuilder sym => CanMux sym BoolType where
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

instance IsExprBuilder sym => CanMux sym (StringType si) where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> stringIte s

instance IsExprBuilder sym => CanMux sym (IEEEFloatType fpp) where
  muxReg s = \_ -> floatIte s

------------------------------------------------------------------------
-- RegValue Vector instance

{-# INLINE muxVector #-}
muxVector :: IsSymInterface sym =>
             sym -> MuxFn p e -> MuxFn p (V.Vector e)
muxVector sym f p x y
  | V.length x == V.length y = V.zipWithM (f p) x y
  | otherwise =
    addFailedAssertion sym
      $ Unsupported "Cannot merge vectors with different dimensions."

instance (IsSymInterface sym, CanMux sym tp) => CanMux sym (VectorType tp) where
  {-# INLINE muxReg #-}
  muxReg s _ = muxVector s (muxReg s (Proxy :: Proxy tp))

------------------------------------------------------------------------
-- RegValue WordMap instance

instance (IsExprBuilder sym, KnownNat w, KnownRepr BaseTypeRepr tp)
  => CanMux sym (WordMapType w tp) where
  {-# INLINE muxReg #-}
  muxReg s _ p = muxWordMap s knownNat knownRepr p

------------------------------------------------------------------------
-- RegValue MatlabChar instance

instance IsSymInterface sym => CanMux sym CharType where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> eqMergeFn s "characters"

------------------------------------------------------------------------
-- RegValue Maybe instance

mergePartExpr :: IsExprBuilder sym
              => sym
              -> (Pred sym -> v -> v -> IO v)
              -> Pred sym
              -> PartExpr (Pred sym) v
              -> PartExpr (Pred sym) v
              -> IO (PartExpr (Pred sym) v)
mergePartExpr sym fn = mergePartial sym (\c a b -> lift (fn c a b))

instance (IsExprBuilder sym, CanMux sym tp) => CanMux sym (MaybeType tp) where
  {-# INLINE muxReg #-}
  muxReg s = \_ -> do
    let f = muxReg s (Proxy :: Proxy tp)
     in mergePartExpr s f

------------------------------------------------------------------------
-- RegValue FunctionHandleType instance

-- TODO: Figure out how to actually compare these.
{-# INLINE muxHandle #-}
muxHandle :: IsExpr (SymExpr sym)
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

newtype RolledType sym nm ctx = RolledType { unroll :: RegValue sym (UnrollType nm ctx) }


{-# INLINE muxRecursive #-}
muxRecursive
   :: IsRecursiveType nm
   => (forall tp. TypeRepr tp -> ValMuxFn sym tp)
   -> SymbolRepr nm
   -> CtxRepr ctx
   -> ValMuxFn sym (RecursiveType nm ctx)
muxRecursive recf = \nm ctx p x y -> do
   RolledType <$> recf (unrollType nm ctx) p (unroll x) (unroll y)

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

-- | Construct a 'VariantType' value by identifying which branch of
--   the variant to construct, and providing a value of the correct type.
injectVariant ::
  IsExprBuilder sym =>
  sym {- ^ symbolic backend -} ->
  CtxRepr ctx {- ^ Types of the variant branches -} ->
  Ctx.Index ctx tp {- ^ Which branch -} ->
  RegValue sym tp  {- ^ The value to inject -} ->
  RegValue sym (VariantType ctx)
injectVariant sym ctxRepr idx val =
  Ctx.generate (Ctx.size ctxRepr) $ \j ->
    case testEquality j idx of
      Just Refl -> VB (PE (truePred sym) val)
      Nothing -> VB Unassigned


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
