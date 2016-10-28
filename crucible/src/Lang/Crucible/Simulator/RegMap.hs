-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.RegMap
-- Description      : Runtime representation of CFG registers
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Register maps hold the values of registers at simulation/run time.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Lang.Crucible.Simulator.RegMap
  ( RegEntry(..)
  , muxRegEntry
  , RegMap(..)
  , regMapSize
  , emptyRegMap
  , regVal
  , regVal'
  , assignReg
  , muxRegForType
  , pushBranchForType
  , abortBranchForType
  , pushBranchRegs
  , abortBranchRegs
  , pushBranchRegEntry
  , abortBranchRegEntry
  , mergeRegs
  , asSymExpr
  , module Lang.Crucible.Simulator.RegValue
  ) where

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.Core (Reg(..))
import           Lang.Crucible.Simulator.ExecutionTree (MuxFn)
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Types
import qualified Lang.Crucible.Utils.SymMultiDimArray as SMDA

------------------------------------------------------------------------
-- RegMap

-- | The value of a register.
data RegEntry sym tp = RegEntry { regType :: (TypeRepr tp)
                                , regValue :: !(RegValue sym tp)
                                }

-- | A set of registers in an execution frame.
newtype RegMap sym (ctx :: Ctx CrucibleType)
      = RegMap (Ctx.Assignment (RegEntry sym) ctx)

regMapSize :: RegMap sym ctx -> Ctx.Size ctx
regMapSize (RegMap s) = Ctx.size s

-- | Create a new set of registers.
emptyRegMap :: RegMap sym EmptyCtx
emptyRegMap = RegMap Ctx.empty

assignReg :: TypeRepr tp
          -> RegValue sym tp
          -> RegMap sym ctx
          -> RegMap sym (ctx ::> tp)
assignReg tp v (RegMap m) =  RegMap (m Ctx.%> RegEntry tp v)
{-# INLINE assignReg #-}

regVal :: RegMap sym ctx
       -> Reg ctx tp
       -> RegValue sym tp
regVal (RegMap a) r = v
  where RegEntry _ v = a Ctx.! regIndex r

regVal' :: RegMap sym ctx
       -> Reg ctx tp
       -> RegEntry sym tp
regVal' (RegMap a) r = a Ctx.! regIndex r


muxConcrete :: (Eq a, Show a) => sym -> ValMuxFn sym (ConcreteType a)
muxConcrete _ _ x y
  | x == y = return x
  | otherwise =
     fail $ unwords ["Attempted to mux distinct concrete values", show x, show y]

muxAny :: IsExprBuilder sym
       => sym
       -> IntrinsicTypes sym
       -> ValMuxFn sym AnyType
muxAny s itefns p (AnyValue tpx x) (AnyValue tpy y)
  | Just Refl <- testEquality tpx tpy =
       AnyValue tpx <$> muxRegForType s itefns tpx p x y
  | otherwise = fail $ unwords ["Attempted to mux ANY values of different runtime type"
                               , show tpx, show tpy
                               ]

muxReference :: IsExprBuilder sym
             => sym
             -> ValMuxFn sym (ReferenceType tp)
muxReference _s _p rx ry
  | Just Refl <- testEquality rx ry = return rx
  | otherwise = fail $ unwords ["Attempted to merge distinct reference cells"]

{-# INLINABLE pushBranchForType #-}
pushBranchForType :: forall sym tp
               . IsExprBuilder sym
              => sym
              -> IntrinsicTypes sym
              -> TypeRepr tp
              -> RegValue sym tp
              -> IO (RegValue sym tp)
pushBranchForType s iTypes p =
  case p of
    IntrinsicRepr nm ->
       case MapF.lookup nm iTypes of
         Just IntrinsicMuxFn -> pushBranchIntrinsic s nm
         Nothing ->
           fail $ unwords ["Unknown intrinsic type:", show nm]

    AnyRepr -> \(AnyValue tpr x) -> AnyValue tpr <$> pushBranchForType s iTypes tpr x

    -- All remaining types do no push branch bookkeeping
    _ -> return

{-# INLINABLE abortBranchForType #-}
abortBranchForType :: forall sym tp
               . IsExprBuilder sym
              => sym
              -> IntrinsicTypes sym
              -> TypeRepr tp
              -> RegValue sym tp
              -> IO (RegValue sym tp)
abortBranchForType s iTypes p =
  case p of
    IntrinsicRepr nm ->
       case MapF.lookup nm iTypes of
         Just IntrinsicMuxFn -> abortBranchIntrinsic s nm
         Nothing ->
           fail $ unwords ["Unknown intrinsic type:", show nm]

    AnyRepr -> \(AnyValue tpr x) -> AnyValue tpr <$> abortBranchForType s iTypes tpr x

    -- All remaining types do no abort branch bookkeeping
    _ -> return

{-# INLINABLE muxRegForType #-}
muxRegForType :: forall sym tp
               . IsExprBuilder sym
              => sym
              -> IntrinsicTypes sym
              -> TypeRepr tp
              -> ValMuxFn sym tp
muxRegForType s itefns p =
  case p of
     UnitRepr          -> muxReg s p
     NatRepr           -> muxReg s p
     IntegerRepr       -> muxReg s p
     RealValRepr       -> muxReg s p
     ComplexRealRepr   -> muxReg s p
     CharRepr          -> muxReg s p
     BoolRepr          -> muxReg s p
     IntWidthRepr      -> muxReg s p
     UIntWidthRepr     -> muxReg s p
     StringRepr        -> muxReg s p

     MatlabIntRepr     -> muxReg s p
     MatlabUIntRepr    -> muxReg s p
     MatlabIntArrayRepr  -> muxReg s p
     MatlabUIntArrayRepr -> muxReg s p

     ConcreteRepr TypeableType -> muxConcrete s
     AnyRepr -> muxAny s itefns
     StructRepr  ctx -> muxStruct    (muxRegForType s itefns) ctx
     VariantRepr ctx -> muxVariant s (muxRegForType s itefns) ctx
     ReferenceRepr _x -> muxReference s
     WordMapRepr w tp -> muxWordMap s w tp
     BVRepr w ->
       case isPosNat w of
         Nothing -> \_ x _ -> return x
         Just LeqProof -> bvIte s
     FunctionHandleRepr _ _ -> muxReg s p

     MaybeRepr r          -> mergePartExpr s (muxRegForType s itefns r)
     VectorRepr r         -> muxVector (muxRegForType s itefns r)
     StringMapRepr r      -> muxStringMap s (muxRegForType s itefns r)
     MultiDimArrayRepr r  -> mdaMuxFn (muxRegForType s itefns r)
     SymbolicMultiDimArrayRepr _ -> SMDA.muxArray s
     SymbolicArrayRepr{}         -> arrayIte s
     SymbolicStructRepr{}        -> structIte s
     MatlabSymbolicIntArrayRepr -> muxReg s p
     MatlabSymbolicUIntArrayRepr -> muxReg s p
     RecursiveRepr nm -> muxRecursive (muxRegForType s itefns) nm
     IntrinsicRepr nm ->
       case MapF.lookup nm itefns of
         Just IntrinsicMuxFn -> muxIntrinsic s nm
         Nothing ->
           fail $ unwords ["Unknown intrinsic type:", show nm]

     FloatRepr _ -> fail $ "Float types are not supported by muxRegForType'"

-- | Mux two register entries.
{-# INLINE muxRegEntry #-}
muxRegEntry :: (IsExprBuilder sym)
             => sym
             -> IntrinsicTypes sym
             -> MuxFn (Pred sym) (RegEntry sym tp)
muxRegEntry sym iteFns pp (RegEntry rtp x) (RegEntry _ y) = do
  RegEntry rtp <$> muxRegForType sym iteFns rtp pp x y

pushBranchRegEntry
             :: (IsExprBuilder sym)
             => sym
             -> IntrinsicTypes sym
             -> RegEntry sym tp
             -> IO (RegEntry sym tp)
pushBranchRegEntry sym iTypes (RegEntry tp x) =
  RegEntry tp <$> pushBranchForType sym iTypes tp x

abortBranchRegEntry
             :: (IsExprBuilder sym)
             => sym
             -> IntrinsicTypes sym
             -> RegEntry sym tp
             -> IO (RegEntry sym tp)
abortBranchRegEntry sym iTypes (RegEntry tp x) =
  RegEntry tp <$> abortBranchForType sym iTypes tp x


{-# INLINE mergeRegs #-}
mergeRegs :: (IsExprBuilder sym)
          => sym
          -> IntrinsicTypes sym
          -> MuxFn (Pred sym) (RegMap sym ctx)
mergeRegs sym iTypes pp (RegMap rx) (RegMap ry) = do
  RegMap <$> Ctx.zipWithM (muxRegEntry sym iTypes pp) rx ry

{-# INLINE pushBranchRegs #-}
pushBranchRegs :: forall sym ctx
           . (IsExprBuilder sym)
          => sym
          -> IntrinsicTypes sym
          -> RegMap sym ctx
          -> IO (RegMap sym ctx)
pushBranchRegs sym iTypes (RegMap rx) =
  RegMap <$> traverseFC (pushBranchRegEntry sym iTypes) rx

{-# INLINE abortBranchRegs #-}
abortBranchRegs :: forall sym ctx
           . (IsExprBuilder sym)
          => sym
          -> IntrinsicTypes sym
          -> RegMap sym ctx
          -> IO (RegMap sym ctx)
abortBranchRegs sym iTypes (RegMap rx) =
  RegMap <$> traverseFC (abortBranchRegEntry sym iTypes) rx

------------------------------------------------------------------------
-- Coerce a RegEntry to a SymExpr

asSymExpr :: RegEntry sym tp -- ^ RegEntry to examine
          -> (forall bt. tp ~ BaseToType bt => SymExpr sym bt -> a)
               -- ^ calculate final value when the register is a SymExpr
          -> a -- ^ final value to use if the register entry is not a SymExpr
          -> a
asSymExpr (RegEntry tp v) just nothing =
  case tp of
     NatRepr           -> just v
     IntegerRepr       -> just v
     RealValRepr       -> just v
     ComplexRealRepr   -> just v
     BoolRepr          -> just v
     BVRepr _w         -> just v
     _ -> nothing
