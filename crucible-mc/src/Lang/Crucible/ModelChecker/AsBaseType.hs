{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.AsBaseType
-- Description      : Functions and type families to turn Crucible contexts into What4 contexts
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.AsBaseType
  ( AsBaseType',
    AsBaseTypes,
    asBaseTypeRepr,
    asBaseTypeReprs,
    asBaseTypeNames,
  )
where

import Data.Functor.Const
import qualified Data.Parameterized.Context as Ctx
import Lang.Crucible.CFG.Core hiding (Expr)
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)

-- FIXME: try using Lang.Crucible.Types.AsBaseType

-- | The partial @AsBaseType@ type family maps Crucible types to What4 types.
-- All base types are accounted for, for other types, we map it to the type that
-- is convenient for the model checker.
type family AsBaseType' (c :: CrucibleType) :: BaseType where
  AsBaseType' BoolType = BaseBoolType
  AsBaseType' IntegerType = BaseIntegerType
  AsBaseType' NatType = BaseNatType
  AsBaseType' RealValType = BaseRealType
  AsBaseType' (LLVMPointerType w) = BaseBVType w

-- | @AsBaseTypes@ is essentially a type-level "fmap", but specialized to the
-- @CrucibleType@ to @BaseType@ transformation, since we can't have unsaturated
-- type families.
type family AsBaseTypes (c :: Ctx CrucibleType) :: Ctx BaseType where
  AsBaseTypes EmptyCtx = EmptyCtx
  AsBaseTypes (c ::> ctp) = AsBaseTypes c ::> AsBaseType' ctp

-- | @asBaseTypeRepr@ implements the Crucible to What4 type translation at the
-- representation level.
asBaseTypeRepr :: TypeRepr c -> BaseTypeRepr (AsBaseType' c)
asBaseTypeRepr BoolRepr = BaseBoolRepr
asBaseTypeRepr IntegerRepr = BaseIntegerRepr
asBaseTypeRepr NatRepr = BaseNatRepr
asBaseTypeRepr RealValRepr = BaseRealRepr
asBaseTypeRepr (LLVMPointerRepr w) = BaseBVRepr w
asBaseTypeRepr tp = error $ "baseTypeReprOfTypeRepr: missing " ++ show tp

asBaseTypeReprs ::
  CtxRepr init ->
  Ctx.Assignment BaseTypeRepr (AsBaseTypes init)
asBaseTypeReprs ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctx' ctp -> Ctx.extend (asBaseTypeReprs ctx') (asBaseTypeRepr ctp)

-- | @asBaseTypeNames@ is an unfortunate non-free no-op to convince the type
-- checker that a bunch of names for a Crucible type context can be seen as a
-- bunch of names for a What4 type context.  The other equivalent option would
-- be to re-run @namesOfCrucibleTypes@, which would be about the same amount of
-- work...
asBaseTypeNames ::
  Ctx.Assignment (Const String) init ->
  Ctx.Assignment (Const String) (AsBaseTypes init)
asBaseTypeNames ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctx' (Const s) -> Ctx.extend (asBaseTypeNames ctx') (Const s)
