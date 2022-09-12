----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.RegMap
-- Description      : Runtime representation of CFG registers
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Register maps hold the values of registers at simulation/run time.
------------------------------------------------------------------------
{-# LANGUAGE AllowAmbiguousTypes #-} -- for @reg@
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
  , reg
  , regVal
  , regVal'
  , assignReg
  , assignReg'
  , appendRegs
  , takeRegs
  , unconsReg
  , muxRegForType
  , muxReference
  , eqReference
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

import           What4.Interface
import           What4.WordMap

import           Lang.Crucible.CFG.Core (Reg(..))
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.MuxTree
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic
import qualified Prettyprinter as PP
import Data.Parameterized.Context (toVector)
import qualified Data.Vector as Vector
import qualified Text.Printf as Text

------------------------------------------------------------------------
-- RegMap

-- | The value of a register.
data RegEntry sym tp = RegEntry { regType :: !(TypeRepr tp)
                                , regValue :: !(RegValue sym tp)
                                }

instance IsExpr (SymExpr sym) => PP.Pretty (RegEntry sym tp) where
  pretty (RegEntry tp val) = case tp of
    UnitRepr -> PP.parens $ PP.pretty "RegEntry(Unit)" PP.<+> PP.pretty val
    IntrinsicRepr symbol _ -> PP.parens $ PP.pretty "RegEntry(Intrinsic)" PP.<+> PP.pretty (show symbol)
    CharRepr -> PP.parens $ PP.pretty "RegEntry(Char8)" PP.<+> PP.pretty val
    FunctionHandleRepr ptr1 ptr2 -> PP.parens $ PP.pretty "RegEntry(FunctionHandle)" PP.<+> PP.pretty (show ptr1) PP.<+> PP.pretty (show ptr2)
    NatRepr -> PP.parens $ PP.pretty "RegEntry(Nat)" PP.<+> printSymNat val
    BVRepr w -> PP.parens $ PP.pretty "RegEntry(BV)" PP.<+> PP.pretty (show w) PP.<+> printSymExpr val
    BoolRepr -> PP.parens $ PP.pretty "RegEntry(Bool)" PP.<+> printSymExpr val
    FloatRepr DoubleFloatRepr -> PP.parens $ PP.pretty "RegEntry(Float Double)" PP.<+> printSymExpr val
    FloatRepr SingleFloatRepr -> PP.parens $ PP.pretty "RegEntry(Float Single)" PP.<+> printSymExpr val
    FloatRepr HalfFloatRepr -> PP.parens $ PP.pretty "RegEntry(Float Half)" PP.<+> printSymExpr val
    FloatRepr QuadFloatRepr -> PP.parens $ PP.pretty "RegEntry(Float Quad)" PP.<+> printSymExpr val
    FloatRepr X86_80FloatRepr -> PP.parens $ PP.pretty "RegEntry(Float X86_80)" PP.<+> printSymExpr val
    FloatRepr DoubleDoubleFloatRepr -> PP.parens $ PP.pretty "RegEntry(Float DoubleDouble)" PP.<+> printSymExpr val
    StringRepr UnicodeRepr -> PP.parens $ PP.pretty "RegEntry(String Unicode)" PP.<+> printSymExpr val
    StringRepr Char8Repr -> PP.parens $ PP.pretty "RegEntry(String Char8)" PP.<+> printSymExpr val
    StringRepr Char16Repr -> PP.parens $ PP.pretty "RegEntry(String Char16)" PP.<+> printSymExpr val
    VectorRepr elemType -> PP.parens $ PP.pretty "RegEntry(Vector)" PP.<+> PP.pretty (show elemType) -- PP.<+> printSymExpr val
    _ -> error $ Text.printf "RegEntry: not a unit type Regentry tp=%v" (show tp)

-- | A set of registers in an execution frame.
newtype RegMap sym (ctx :: Ctx CrucibleType)
      = RegMap { regMap :: Ctx.Assignment (RegEntry sym) ctx }

instance IsExpr (SymExpr sym) => PP.Pretty (RegMap sym ctx) where
  pretty (RegMap m) = PP.pretty "RegMap" PP.<+> PP.vcat (Vector.toList (toVector m PP.pretty))

regMapSize :: RegMap sym ctx -> Ctx.Size ctx
regMapSize (RegMap s) = Ctx.size s

-- | Create a new set of registers.
emptyRegMap :: RegMap sym EmptyCtx
emptyRegMap = RegMap Ctx.empty

assignReg :: TypeRepr tp
          -> RegValue sym tp
          -> RegMap sym ctx
          -> RegMap sym (ctx ::> tp)
assignReg tp v (RegMap m) =  RegMap (m Ctx.:> RegEntry tp v)
{-# INLINE assignReg #-}

assignReg' :: RegEntry sym tp
           -> RegMap sym ctx
           -> RegMap sym (ctx ::> tp)
assignReg' v (RegMap m) =  RegMap (m Ctx.:> v)
{-# INLINE assignReg' #-}


appendRegs ::
  RegMap sym ctx ->
  RegMap sym ctx' ->
  RegMap sym (ctx <+> ctx')
appendRegs (RegMap m1) (RegMap m2) = RegMap (m1 Ctx.<++> m2)

unconsReg ::
  RegMap sym (ctx ::> tp) ->
  (RegMap sym ctx, RegEntry sym tp)
unconsReg (RegMap (hd Ctx.:> tl)) = (RegMap hd, tl)

takeRegs ::
  Ctx.Size ctx ->
  Ctx.Size ctx' ->
  RegMap sym (ctx <+> ctx') ->
  RegMap sym ctx
takeRegs sz sz' (RegMap m) = RegMap (Ctx.take sz sz' m)

reg :: forall n sym ctx tp. Ctx.Idx n ctx tp => RegMap sym ctx -> RegValue sym tp
reg m = regVal m (Reg (Ctx.natIndex @n))

regVal :: RegMap sym ctx
       -> Reg ctx tp
       -> RegValue sym tp
regVal (RegMap a) r = v
  where RegEntry _ v = a Ctx.! regIndex r

regVal' :: RegMap sym ctx
       -> Reg ctx tp
       -> RegEntry sym tp
regVal' (RegMap a) r = a Ctx.! regIndex r


muxAny :: IsSymInterface sym
       => sym
       -> IntrinsicTypes sym
       -> ValMuxFn sym AnyType
muxAny s itefns p (AnyValue tpx x) (AnyValue tpy y)
  | Just Refl <- testEquality tpx tpy =
       AnyValue tpx <$> muxRegForType s itefns tpx p x y
  | otherwise = throwUnsupported s $ unwords
                      ["Attempted to mux ANY values of different runtime type"
                      , show tpx, show tpy
                      ]

muxReference ::
  IsSymInterface sym => sym -> ValMuxFn sym (ReferenceType tp)
muxReference s = mergeMuxTree s

eqReference ::
  IsSymInterface sym =>
  sym ->
  RegValue sym (ReferenceType tp) ->
  RegValue sym (ReferenceType tp) ->
  IO (Pred sym)
eqReference sym = muxTreeEq sym


{-# INLINABLE pushBranchForType #-}
pushBranchForType :: forall sym tp
               . IsSymInterface sym
              => sym
              -> IntrinsicTypes sym
              -> TypeRepr tp
              -> RegValue sym tp
              -> IO (RegValue sym tp)
pushBranchForType s iTypes p =
  case p of
    IntrinsicRepr nm ctx ->
       case MapF.lookup nm iTypes of
         Just IntrinsicMuxFn -> pushBranchIntrinsic s iTypes nm ctx
         Nothing -> \_ ->
           panic "RegMap.pushBranchForType"
              [ "Unknown intrinsic type:"
              , "*** Name: " ++ show nm
              ]

    AnyRepr -> \(AnyValue tpr x) -> AnyValue tpr <$> pushBranchForType s iTypes tpr x

    -- All remaining types do no push branch bookkeeping
    _ -> return

{-# INLINABLE abortBranchForType #-}
abortBranchForType :: forall sym tp
               . IsSymInterface sym
              => sym
              -> IntrinsicTypes sym
              -> TypeRepr tp
              -> RegValue sym tp
              -> IO (RegValue sym tp)
abortBranchForType s iTypes p =
  case p of
    IntrinsicRepr nm ctx ->
       case MapF.lookup nm iTypes of
         Just IntrinsicMuxFn -> abortBranchIntrinsic s iTypes nm ctx
         Nothing ->
           panic "RegMap.abortBranchForType"
              [ "Unknown intrinsic type:"
              , "*** Name: " ++ show nm
              ]
    AnyRepr -> \(AnyValue tpr x) ->
      AnyValue tpr <$> abortBranchForType s iTypes tpr x

    -- All remaining types do no abort branch bookkeeping
    _ -> return

{-# INLINABLE muxRegForType #-}
muxRegForType :: forall sym tp
               . IsSymInterface sym
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
     FloatRepr _       -> muxReg s p
     ComplexRealRepr   -> muxReg s p
     CharRepr          -> muxReg s p
     BoolRepr          -> muxReg s p
     StringRepr _      -> muxReg s p
     IEEEFloatRepr _p  -> muxReg s p

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
     VectorRepr r         -> muxVector s (muxRegForType s itefns r)
     SequenceRepr _r      -> muxSymSequence s
     StringMapRepr r      -> muxStringMap s (muxRegForType s itefns r)
     SymbolicArrayRepr{}         -> arrayIte s
     SymbolicStructRepr{}        -> structIte s
     RecursiveRepr nm ctx -> muxRecursive (muxRegForType s itefns) nm ctx
     IntrinsicRepr nm ctx ->
       case MapF.lookup nm itefns of
         Just IntrinsicMuxFn -> muxIntrinsic s itefns nm ctx
         Nothing -> \_ _ _ ->
           panic "RegMap.muxRegForType"
              [ "Unknown intrinsic type:"
              , "*** Name: " ++ show nm
              ]

-- | Mux two register entries.
{-# INLINE muxRegEntry #-}
muxRegEntry :: IsSymInterface sym
             => sym
             -> IntrinsicTypes sym
             -> MuxFn (Pred sym) (RegEntry sym tp)
muxRegEntry sym iteFns pp (RegEntry rtp x) (RegEntry _ y) = do
  RegEntry rtp <$> muxRegForType sym iteFns rtp pp x y

pushBranchRegEntry
             :: (IsSymInterface sym)
             => sym
             -> IntrinsicTypes sym
             -> RegEntry sym tp
             -> IO (RegEntry sym tp)
pushBranchRegEntry sym iTypes (RegEntry tp x) =
  RegEntry tp <$> pushBranchForType sym iTypes tp x

abortBranchRegEntry
             :: (IsSymInterface sym)
             => sym
             -> IntrinsicTypes sym
             -> RegEntry sym tp
             -> IO (RegEntry sym tp)
abortBranchRegEntry sym iTypes (RegEntry tp x) =
  RegEntry tp <$> abortBranchForType sym iTypes tp x


{-# INLINE mergeRegs #-}
mergeRegs :: (IsSymInterface sym)
          => sym
          -> IntrinsicTypes sym
          -> MuxFn (Pred sym) (RegMap sym ctx)
mergeRegs sym iTypes pp (RegMap rx) (RegMap ry) = do
  RegMap <$> Ctx.zipWithM (muxRegEntry sym iTypes pp) rx ry

{-# INLINE pushBranchRegs #-}
pushBranchRegs :: forall sym ctx
           . (IsSymInterface sym)
          => sym
          -> IntrinsicTypes sym
          -> RegMap sym ctx
          -> IO (RegMap sym ctx)
pushBranchRegs sym iTypes (RegMap rx) =
  RegMap <$> traverseFC (pushBranchRegEntry sym iTypes) rx

{-# INLINE abortBranchRegs #-}
abortBranchRegs :: forall sym ctx
           . (IsSymInterface sym)
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
     IntegerRepr       -> just v
     RealValRepr       -> just v
     ComplexRealRepr   -> just v
     BoolRepr          -> just v
     BVRepr _w         -> just v
     IEEEFloatRepr _p  -> just v
     _ -> nothing
