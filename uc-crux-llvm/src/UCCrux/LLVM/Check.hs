{-
Module       : UCCrux.LLVM.Check
Description  : Check whether constraints hold
Copyright    : (c) Galois, Inc 2022
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

Create predicates that represent whether or not a set of constraints
('ConstrainedShape') hold of some Crucible value ('Crucible.RegValue') in some
LLVM memory ('LLVMMem.MemImpl'). These predicates are used in "check overrides"
("UCCrux.LLVM.Overrides.Check").
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Check
  ( CheckedConstraint(..),
    SomeCheckedConstraint(..),
    SomeCheckedConstraint'(..),
    checkConstrainedShape,
    checkConstrainedShapes,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)
import           Control.Lens ((^.), (%~))
import           Control.Monad (foldM, unless)
import           Data.Function ((&))
import           Data.Foldable.WithIndex (FoldableWithIndex, ifoldrM)
import           Data.Functor.Compose (Compose(Compose))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector as Vec

import           Data.Parameterized.Classes (IndexF)
import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.TraversableFC.WithIndex (FoldableFCWithIndex, ifoldrMFC)
import           Data.Parameterized.Some (Some(Some), viewSome)
import qualified Data.Parameterized.Vector as PVec

-- what4
import           What4.Interface (Pred)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (Constraint, ShapeConstraint(Initialized), ConstrainedShape(..))
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.Cursor (Selector, selectorCursor)
import qualified UCCrux.LLVM.Cursor as Cursor
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(SomeIndex), translateIndex)
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr, MapToCrucibleType, ToCrucibleType, pointedToType, arrayElementType)
import qualified UCCrux.LLVM.Mem as Mem
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.Setup.Constraints (constraintToPred)
{- ORMOLU_ENABLE -}


-- | A constraint, together with where it was applied and the resulting 'Pred'
-- it was \"compiled\" to.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data CheckedConstraint m sym (argTypes :: Ctx (FullType m)) inTy atTy
  = CheckedConstraint
      { -- | The 'Constraint' that was applied at this 'Selector' to yield this
        -- 'Pred'
        checkedConstraint :: Either (ShapeConstraint m atTy) (Constraint m atTy),
        -- | The location in an argument or global variable where this
        -- 'Constraint' was applied
        checkedSelector :: Selector m argTypes inTy atTy,
        -- | The \"compiled\"/applied form of the 'Constraint'
        checkedPred :: Pred sym
      }

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data SomeCheckedConstraint m sym (argTypes :: Ctx (FullType m)) =
  forall inTy atTy.
    SomeCheckedConstraint (CheckedConstraint m sym argTypes inTy atTy)

data SomeCheckedConstraint' m =
  forall sym argTypes inTy atTy.
    SomeCheckedConstraint' (CheckedConstraint m sym argTypes inTy atTy)

-- | Helper, not exported
ifoldMapM ::
  FoldableWithIndex i t =>
  Monoid m =>
  Monad f =>
  (i -> a -> f m) ->
  t a ->
  f m
ifoldMapM f = ifoldrM (\i x acc -> fmap (<> acc) (f i x)) mempty

-- | Helper, not exported
ifoldMapMFC ::
  FoldableFCWithIndex t =>
  Monoid m =>
  Monad g =>
  (forall x. IndexF (t f z) x -> f x -> g m) ->
  t f z ->
  g m
ifoldMapMFC f = ifoldrMFC (\i x acc -> fmap (<> acc) (f i x)) mempty

-- | Create predicates that check that a Crucible(-LLVM) value conforms to the
-- 'ConstrainedShape'.
checkConstrainedShape ::
  forall arch m sym argTypes inTy atTy.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  -- | Selector for provenance information
  Selector m argTypes inTy atTy ->
  ConstrainedShape m atTy ->
  FullTypeRepr m atTy ->
  Crucible.RegValue sym (ToCrucibleType arch atTy) ->
  IO (Seq (Some (CheckedConstraint m sym argTypes inTy)))
checkConstrainedShape modCtx sym mem selector cShape fullTypeRepr val =
  case getConstrainedShape cShape of
    Shape.ShapeInt (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapeFloat (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapePtr (Compose cs) Shape.ShapeUnallocated ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapePtr (Compose cs) Shape.ShapeAllocated{} ->
      -- TODO: How to actually tell if the pointer points to something of the
      -- right size? Might be something in MemModel.* that could help?
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapePtr (Compose cs) (Shape.ShapeInitialized subShapes) ->
      do -- TODO: Is there code from Setup that helps with the other addresses?
         -- (Look at 'pointerRange'?)
         unless (Seq.length subShapes == 1) $
           Unimplemented.unimplemented
             "checkConstrainedShape"
             Unimplemented.CheckPrecondsPtrArray
         let mts = modCtx ^. moduleTypes
         (ptdToPred, mbPtdToVal) <- Mem.loadRaw' modCtx sym mem mts val fullTypeRepr
         let shape = ConstrainedShape (subShapes `Seq.index` 0)
         let ptdToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
         let ptdToSelector = selector & selectorCursor %~ Cursor.deepenPtr mts
         subs <-
           case mbPtdToVal of
             Nothing -> pure Seq.empty
             Just ptdToVal ->
               checkConstrainedShape modCtx sym mem ptdToSelector shape ptdToRepr ptdToVal
         here <- constraintsToSomePreds fullTypeRepr selector cs val
         let ptdToConstraint =
               CheckedConstraint
                 { checkedConstraint =
                     Left (Initialized (Seq.length subShapes)),
                   checkedSelector = selector,
                   checkedPred = ptdToPred
                 }
         return (Some ptdToConstraint Seq.<| here <> subs)
    Shape.ShapeFuncPtr (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapeOpaquePtr (Compose cs) ->
      constraintsToSomePreds fullTypeRepr selector cs val
    Shape.ShapeArray (Compose cs) _ subShapes ->
      (<>)
      <$> constraintsToSomePreds fullTypeRepr selector cs val
      <*> ifoldMapM
            (\i shape ->
               checkConstrainedShape
                 modCtx
                 sym
                 mem
                 (selector &
                  selectorCursor %~
                  (\c ->
                    Fin.viewFin
                      (\i' -> Cursor.deepenArray i' (PVec.length subShapes) c)
                      i))
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! fromIntegral (Fin.finToNat i)))
            subShapes
    Shape.ShapeUnboundedArray (Compose cs) subShapes ->
      (<>)
      <$> constraintsToSomePreds fullTypeRepr selector cs val
      <*> ifoldMapM
            (\i shape ->
               checkConstrainedShape
                 modCtx
                 sym
                 mem
                 (Unimplemented.unimplemented
                    "checkConstrainedShape"
                    Unimplemented.NonEmptyUnboundedSizeArrays)
                 (ConstrainedShape shape)
                 (arrayElementType fullTypeRepr)
                 (val Vec.! i))
            subShapes
    Shape.ShapeStruct (Compose cs) _ ->
      (<>)
      <$> constraintsToSomePreds fullTypeRepr selector cs val
      <*> Unimplemented.unimplemented
            "checkConstrainedShape"
            Unimplemented.CheckPrecondsStruct

  where
    foldMapM :: forall t f m' a. Foldable t => Monoid m' => Monad f => (a -> f m') -> t a -> f m'
    foldMapM f = foldM (\acc -> fmap (<> acc) . f) mempty

    constraintsToSomePreds ::
      forall atTy'.
      FullTypeRepr m atTy' ->
      Selector m argTypes inTy atTy' ->
      [Constraint m atTy'] ->
      Crucible.RegValue sym (ToCrucibleType arch atTy') ->
      IO (Seq (Some (CheckedConstraint m sym argTypes inTy)))
    constraintsToSomePreds ftRepr selector_ cs v =
      fmap (fmap Some) (constraintsToPreds ftRepr selector_ cs v)

    constraintsToPreds ::
      forall atTy'.
      FullTypeRepr m atTy' ->
      Selector m argTypes inTy atTy' ->
      [Constraint m atTy'] ->
      Crucible.RegValue sym (ToCrucibleType arch atTy') ->
      IO (Seq (CheckedConstraint m sym argTypes inTy atTy'))
    constraintsToPreds ftRepr selector_ cs v =
      foldMapM
        (\c ->
          Seq.singleton . CheckedConstraint (Right c) selector_ <$>
            constraintToPred modCtx sym c ftRepr v)
        cs

-- | Create predicates that check that an list of Crucible(-LLVM) values conform
-- to a list of 'ConstrainedShape's.
checkConstrainedShapes ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Ctx.Assignment (ConstrainedShape m) argTypes ->
  Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch argTypes) ->
  IO (Seq (SomeCheckedConstraint m sym argTypes))
checkConstrainedShapes modCtx sym mem argFTys constraints args =
  ifoldMapMFC
    (\idx constraint ->
      do SomeIndex idx' Refl <-
          pure $
            let sz = Ctx.size constraints
            in translateIndex modCtx sz idx
         let arg = args Ctx.! idx'
         let fTy = argFTys Ctx.! idx
         fmap (viewSome SomeCheckedConstraint) <$>
           checkConstrainedShape
             modCtx
             sym
             mem
             (Cursor.SelectArgument idx (Cursor.Here fTy))
             constraint
             fTy
             (Crucible.regValue arg))
    constraints
