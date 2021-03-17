{-
Module       : UCCrux.LLVM.Constraints
Description  : Constraints
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Constraints
  ( -- * Types of constraints
    ShapeConstraint (..),
    Constraint (..),
    RelationalConstraint (..),

    -- * Collections of constraints
    Constraints (..),
    argConstraints,
    globalConstraints,
    relationalConstraints,
    emptyConstraints,
    ppConstraints,
    isEmpty,

    -- * 'ConstrainedShape'
    ConstrainedShape (..),
    expand,
    ExpansionError (..),
    ppExpansionError,

    -- * 'NewConstraint'
    NewConstraint (..),
    addConstraint,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (Simple, Lens, lens, (%~), (%%~), (.~), (^.))
import           Data.Bifunctor (first)
import           Data.BitVector.Sized (BV)
import           Data.Coerce (coerce)
import           Data.Function ((&))
import           Data.Functor.Compose (Compose(..))
import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vec
import           Data.Void as Void
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (IxedF'(ixF'))
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC (allFC, fmapFC, toListFC)

import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment)

import           UCCrux.LLVM.Cursor (Selector(..), SomeInSelector(SomeInSelector), seekType)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.Shape (Shape, ShapeSeekError)
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.FullType.ModuleTypes (ModuleTypes)
import           UCCrux.LLVM.FullType.MemType (asFullType)
import           UCCrux.LLVM.FullType.Type (FullType(..), FullTypeRepr(FTPtrRepr))
{- ORMOLU_ENABLE -}

--------------------------------------------------------------------------------

-- * Types of constraints

data ShapeConstraint (m :: Type) (atTy :: FullType m) where
  -- | This pointer is not null, and has space for at least this many elements
  --
  -- Invariant: argument should be positive.
  Allocated :: !Int -> ShapeConstraint m ('FTPtr ft)
  -- | This pointer points to initialized memory with at least this many elements
  --
  -- Invariant: argument should be positive.
  Initialized :: !Int -> ShapeConstraint m ('FTPtr ft)

instance Eq (ShapeConstraint m atTy) where
  c1 == c2 =
    case (c1, c2) of
      (Allocated n1, Allocated n2) -> n1 == n2
      (Initialized n1, Initialized n2) -> n1 == n2
      _ -> False

data Constraint (m :: Type) (atTy :: FullType m) where
  -- | This pointer has at least this alignment
  Aligned :: !Alignment -> Constraint m ('FTPtr ft)
  -- | This comparison holds.
  BVCmp :: !L.ICmpOp -> !(BV w) -> Constraint m ('FTInt w)

instance Eq (Constraint m atTy) where
  c1 == c2 =
    case (c1, c2) of
      (Aligned n1, Aligned n2) -> n1 == n2
      (BVCmp op1 bv1, BVCmp op2 bv2) -> op1 == op2 && bv1 == bv2

ppConstraint :: Constraint m ft -> Doc Void
ppConstraint =
  \case
    Aligned alignment ->
      PP.pretty "is aligned to " <> PP.viaShow (fromAlignment alignment)
    BVCmp L.Ieq bv -> PP.pretty "is equal to " <> PP.viaShow bv
    BVCmp L.Ine bv -> PP.pretty "is not equal to " <> PP.viaShow bv
    BVCmp L.Iult bv -> PP.pretty "is (unsigned) less than " <> PP.viaShow bv
    BVCmp L.Iule bv -> PP.pretty "is (unsigned) less than or equal to " <> PP.viaShow bv
    BVCmp L.Iugt bv -> PP.pretty "is (unsigned) greater than " <> PP.viaShow bv
    BVCmp L.Iuge bv -> PP.pretty "is (unsigned) greater than or equal to " <> PP.viaShow bv
    BVCmp L.Islt bv -> PP.pretty "is (signed) less than " <> PP.viaShow bv
    BVCmp L.Isle bv -> PP.pretty "is (signed) less than or equal to " <> PP.viaShow bv
    BVCmp L.Isgt bv -> PP.pretty "is (signed) greater than " <> PP.viaShow bv
    BVCmp L.Isge bv -> PP.pretty "is (signed) greater than or equal to " <> PP.viaShow bv

-- | A (possibly) \"relational\" constraint across several values.
data RelationalConstraint m argTypes
  = -- | The first argument (a bitvector) is equal to the size of the allocation
    -- pointed to by the second
    forall inTy inTy' ft ft'.
    SizeOfAllocation
      (Selector m argTypes inTy ('FTInt ft))
      (Selector m argTypes inTy' ('FTPtr ft'))

--------------------------------------------------------------------------------

-- * Collections of constraints

data Constraints m argTypes = Constraints
  { _argConstraints :: Ctx.Assignment (ConstrainedShape m) argTypes,
    _globalConstraints :: Map L.Symbol (Some (ConstrainedShape m)),
    _relationalConstraints :: [RelationalConstraint m argTypes]
  }

argConstraints :: Simple Lens (Constraints m argTypes) (Ctx.Assignment (ConstrainedShape m) argTypes)
argConstraints = lens _argConstraints (\s v -> s {_argConstraints = v})

globalConstraints :: Simple Lens (Constraints m globalTypes) (Map L.Symbol (Some (ConstrainedShape m)))
globalConstraints = lens _globalConstraints (\s v -> s {_globalConstraints = v})

relationalConstraints :: Simple Lens (Constraints m argTypes) [RelationalConstraint m argTypes]
relationalConstraints = lens _relationalConstraints (\s v -> s {_relationalConstraints = v})

emptyArgConstraints ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Ctx.Assignment (ConstrainedShape m) argTypes
emptyArgConstraints argTypes =
  fmapFC
    ( \argType ->
        ConstrainedShape
          (fmapFC (\_ -> Compose []) $ Shape.minimal argType)
    )
    argTypes

emptyConstraints ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Constraints m argTypes
emptyConstraints argTypes =
  Constraints
    { _argConstraints = emptyArgConstraints argTypes,
      _globalConstraints = Map.empty,
      _relationalConstraints = []
    }

_oneArgumentConstraint ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Ctx.Index argTypes inTy ->
  ConstrainedShape m inTy ->
  Constraints m argTypes
_oneArgumentConstraint argTypes idx shape =
  emptyConstraints argTypes & argConstraints . ixF' idx .~ shape

ppConstraints :: Constraints m argTypes -> Doc Void
ppConstraints (Constraints args globCs relCs) =
  PP.vsep
    ( catMaybes
        [ if Ctx.sizeInt (Ctx.size args) == 0
            then Nothing
            else
              Just $
                nestSep
                  ( PP.pretty "Arguments:" :
                    toListFC
                      (Shape.ppShape ppConstraints' . getConstrainedShape)
                      args
                  ),
          if Map.size globCs == 0
            then Nothing
            else
              Just $
                nestSep
                  [ PP.pretty "Globals: TODO"
                  ],
          if null relCs
            then Nothing
            else
              Just $
                nestSep
                  [ PP.pretty "Relational constraints: TODO"
                  ]
        ]
    )
  where
    ppConstraints' (Compose constraints) = PP.vsep (map ppConstraint constraints)
    nestSep = PP.nest 2 . PP.vsep

isEmpty :: Constraints m argTypes -> Bool
isEmpty (Constraints args globs rels) =
  allFC (Shape.isMinimal (null . getCompose) . getConstrainedShape) args
    && Map.null globs
    && null rels

--------------------------------------------------------------------------------

-- * 'ConstrainedShape'

-- | A specification of the shape of a value and constraints on it.
newtype ConstrainedShape m ft = ConstrainedShape
  {getConstrainedShape :: Shape m (Compose [] (Constraint m)) ft}

instance Eq (ConstrainedShape m ft) where
  ConstrainedShape shape1 == ConstrainedShape shape2 =
    Shape.eqShape (\(Compose c1) (Compose c2) -> c1 == c2) shape1 shape2

joinLeft :: (a -> b) -> Either a (Either b c) -> Either b c
joinLeft f =
  \case
    Left err -> Left (f err)
    Right (Left err) -> Left err
    Right (Right val) -> Right val

data RedundantExpansion
  = AllocateAllocated
  | AllocateInitialized
  | InitializeInitialized

ppRedundantExpansion :: RedundantExpansion -> Text
ppRedundantExpansion =
  Text.pack
    . \case
      AllocateAllocated -> "Tried to allocate an already-allocated chunk"
      AllocateInitialized -> "Tried to allocate an already-initialized chunk"
      InitializeInitialized -> "Tried to initialize an already-initialized chunk"

expand ::
  forall m tag ft.
  ModuleTypes m ->
  (forall ft'. tag ft') ->
  FullTypeRepr m ft ->
  ShapeConstraint m ft ->
  Shape m tag ft ->
  (Maybe RedundantExpansion, Shape m tag ft)
expand mts minimalTag ftRepr shapeConstraint shape =
  let minimalVec :: forall ft'. Int -> FullTypeRepr m ft' -> Vec.Vector (Shape m tag ft')
      minimalVec sz ftr =
        Vec.replicate sz (fmapFC (const minimalTag) $ Shape.minimal ftr)
   in case (ftRepr, shape, shapeConstraint) of
        (FTPtrRepr {}, Shape.ShapePtr tag Shape.ShapeUnallocated, Allocated n) ->
          -- Create a new allocation
          (Nothing, Shape.ShapePtr tag (Shape.ShapeAllocated n))
        (FTPtrRepr ptRepr, Shape.ShapePtr tag Shape.ShapeUnallocated, Initialized n) ->
          -- Create and initialize a new allocation
          ( Nothing,
            Shape.ShapePtr
              tag
              (Shape.ShapeInitialized (minimalVec n (asFullType mts ptRepr)))
          )
        (FTPtrRepr ptRepr, Shape.ShapePtr tag (Shape.ShapeAllocated m), Initialized n) ->
          ( Nothing,
            Shape.ShapePtr
              tag
              ( Shape.ShapeInitialized
                  (minimalVec (max m n) (asFullType mts ptRepr))
              )
          )
        (FTPtrRepr {}, Shape.ShapePtr tag (Shape.ShapeAllocated m), Allocated n) ->
          if m >= n
            then (Just AllocateAllocated, shape) -- There's enough space already
            else -- Grow the allocation
              (Nothing, Shape.ShapePtr tag (Shape.ShapeAllocated n))
        (FTPtrRepr ptRepr, Shape.ShapePtr tag (Shape.ShapeInitialized vec), Allocated n) ->
          if Vec.length vec >= n
            then (Just AllocateInitialized, shape) -- There's enough space already
            else -- Grow the allocation

              ( Nothing,
                Shape.ShapePtr
                  tag
                  ( Shape.ShapeInitialized
                      (vec <> minimalVec (n - Vec.length vec) (asFullType mts ptRepr))
                  )
              )
        (FTPtrRepr ptRepr, Shape.ShapePtr tag (Shape.ShapeInitialized vec), Initialized n) ->
          if Vec.length vec >= n
            then (Just InitializeInitialized, shape) -- There's enough space already
            else -- Grow the allocation

              ( Nothing,
                Shape.ShapePtr
                  tag
                  ( Shape.ShapeInitialized
                      (vec <> minimalVec (n - Vec.length vec) (asFullType mts ptRepr))
                  )
              )

--------------------------------------------------------------------------------

-- * 'NewConstraint'

data ExpansionError
  = ExpRedundant RedundantExpansion
  | ExpShapeSeekError ShapeSeekError

ppExpansionError :: ExpansionError -> Text
ppExpansionError =
  \case
    ExpRedundant redundant -> ppRedundantExpansion redundant
    ExpShapeSeekError ssErr -> Shape.ppShapeSeekError ssErr

-- | A constraint learned by simulating the code
data NewConstraint m argTypes
  = forall atTy. NewShapeConstraint (SomeInSelector m argTypes atTy) (ShapeConstraint m atTy)
  | forall atTy. NewConstraint (SomeInSelector m argTypes atTy) (Constraint m atTy)
  | NewRelationalConstraint (RelationalConstraint m argTypes)

addConstraint ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  ModuleTypes m ->
  Constraints m argTypes ->
  NewConstraint m argTypes ->
  Either ExpansionError (Constraints m argTypes)
addConstraint argTypes mts constraints =
  \case
    NewConstraint (SomeInSelector (SelectGlobal _symbol _cursor)) _constraint ->
      unimplemented "addConstraint" Unimplemented.ConstrainGlobal
    NewShapeConstraint (SomeInSelector (SelectGlobal _symbol _cursor)) _shapeConstraint ->
      unimplemented "addConstraint" Unimplemented.ConstrainGlobal
    NewConstraint (SomeInSelector (SelectArgument idx cursor)) constraint ->
      constraints & argConstraints . ixF' idx
        %%~ ( \(ConstrainedShape shape) ->
                ConstrainedShape
                  <$> first
                    ExpShapeSeekError
                    (fst <$> Shape.modifyTag (coerce (constraint :)) shape cursor)
            )
    NewShapeConstraint (SomeInSelector (SelectArgument idx cursor)) shapeConstraint ->
      constraints & argConstraints . ixF' idx
        %%~ ( \(ConstrainedShape shape) ->
                ConstrainedShape
                  <$> joinLeft
                    ExpShapeSeekError
                    ( let doExpand shape' =
                            case expand mts (Compose []) (seekType mts cursor (argTypes ^. ixF' idx)) shapeConstraint shape' of
                              -- TODO(lb): Maybe warn here, there's a risk of an
                              -- infinite loop if there's a bug in
                              -- classification.
                              (Just _redundant, result) -> Right result
                              (Nothing, result) -> Right result
                       in Shape.modifyA' doExpand shape cursor
                    )
            )
    NewRelationalConstraint relationalConstraint ->
      Right $ constraints & relationalConstraints %~ (relationalConstraint :)
