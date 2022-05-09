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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Constraints
  ( -- * Types of constraints
    ShapeConstraint (..),
    ppShapeConstraint,
    Constraint (..),
    ppConstraint,
    RelationalConstraint (..),

    -- * Collections of constraints
    ConstrainedTypedValue (..),
    Constraints (..),
    argConstraints,
    globalConstraints,
    returnConstraints,
    relationalConstraints,
    emptyConstraints,
    ppConstraints,
    isEmpty,

    -- * 'ConstrainedShape'
    ConstrainedShape (..),
    minimalConstrainedShape,
    expand,
    ExpansionError (..),
    ppExpansionError,

    -- * 'NewConstraint'
    NewConstraint (..),
    addConstraint,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (Simple, Lens, lens, (%~), (%%~), (^.), at)
import qualified Control.Lens as Lens
import           Data.Bifunctor (first)
import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Coerce (coerce)
import           Data.Function ((&))
import           Data.Functor.Compose (Compose(..))
import           Data.Kind (Type)
import           Data.Maybe (catMaybes, fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Void as Void
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.Classes (IxedF'(ixF'))
import           Data.Parameterized.NatRepr (NatRepr, type (<=))
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC (allFC, fmapFC, toListFC)

import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment)

import           UCCrux.LLVM.Context.Module (ModuleContext, funcTypes, globalTypes, moduleTypes)
import           UCCrux.LLVM.Cursor (Cursor, Selector(..), SomeInSelector(SomeInSelector), seekType, checkCompatibility)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(ClobberConstraints))
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Shape (Shape, ShapeSeekError)
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr(FuncSigRepr), ReturnTypeRepr(VoidRepr, NonVoidRepr))
import           UCCrux.LLVM.FullType.Type (FullType(..), FullTypeRepr(FTPtrRepr), ModuleTypes, asFullType)
import           UCCrux.LLVM.Module (GlobalSymbol, globalSymbol, getGlobalSymbol, FuncSymbol, funcSymbol, getFuncSymbol)

{- ORMOLU_ENABLE -}

--------------------------------------------------------------------------------

-- * Types of constraints

-- | A 'ShapeConstraint' describes a constraint on a part of a value\'s memory
-- layout. They're generated in "UCCrux.LLVM.Classify", and applied to a 'Shape'
-- in 'expand'. Basically, if 'UCCrux.LLVM.Classify.classifyBadBehavior' runs
-- into an error that would be fixed by allocating more memory or initializing
-- more memory, it will return one of these to indicate that the appropriate
-- memory model operation should happen next time in
-- "UCCrux.LLVM.Classify.generate".
data ShapeConstraint (m :: Type) (atTy :: FullType m) where
  -- | This pointer is not null, and has space for at least this many elements
  --
  -- Invariant: argument should be positive.
  Allocated :: !Int -> ShapeConstraint m ('FTPtr ft)
  -- | This pointer points to initialized memory with at least this many elements
  --
  -- Invariant: argument should be positive.
  Initialized :: !Int -> ShapeConstraint m ('FTPtr ft)

deriving instance Eq (ShapeConstraint m atTy)

ppShapeConstraint :: ShapeConstraint m atTy -> Doc ann
ppShapeConstraint =
  \case
    Allocated sz ->
      PP.pretty "points to allocated space for"
      PP.<+> PP.viaShow sz
      PP.<+> PP.pretty "elements"
    Initialized sz ->
      PP.pretty "points to"
      PP.<+> PP.viaShow sz
      PP.<+> PP.pretty "initialized elements"

-- | A 'Constraint' is in general, something that can be \"applied\" to a
-- symbolic value to produce a predicate. In practice, these represent
-- \"missing\" function preconditions that are deduced by
-- 'UCCrux.LLVM.Classify.classifyBadBehavior', and are then turned into
-- predicates when generating those arguments in
-- "UCCrux.LLVM.Classify.generate", and assumed in "UCCrux.LLVM.Run.Simulate".
data Constraint (m :: Type) (atTy :: FullType m) where
  -- | This pointer has at least this alignment
  Aligned :: !Alignment -> Constraint m ('FTPtr ft)
  -- | This comparison holds.
  BVCmp :: (1 <= w) => !L.ICmpOp -> !(NatRepr w) -> !(BV w) -> Constraint m ('FTInt w)

instance Eq (Constraint m atTy) where
  c1 == c2 =
    case (c1, c2) of
      (Aligned n1, Aligned n2) -> n1 == n2
      (BVCmp op1 _ bv1, BVCmp op2 _ bv2) -> op1 == op2 && bv1 == bv2

ppConstraint :: Constraint m ft -> Doc ann
ppConstraint =
  \case
    Aligned alignment ->
      PP.pretty "is aligned to " <> PP.viaShow (fromAlignment alignment)
    BVCmp L.Ieq w bv -> PP.pretty "is equal to " <> unsigned w bv
    BVCmp L.Ine w bv -> PP.pretty "is not equal to " <> unsigned w bv
    BVCmp L.Iult w bv -> PP.pretty "is (unsigned) less than " <> unsigned w bv
    BVCmp L.Iule w bv -> PP.pretty "is (unsigned) less than or equal to " <> unsigned w bv
    BVCmp L.Iugt w bv -> PP.pretty "is (unsigned) greater than " <> unsigned w bv
    BVCmp L.Iuge w bv -> PP.pretty "is (unsigned) greater than or equal to " <> unsigned w bv
    BVCmp L.Islt w bv -> PP.pretty "is (signed) less than " <> signed w bv
    BVCmp L.Isle w bv -> PP.pretty "is (signed) less than or equal to " <> signed w bv
    BVCmp L.Isgt w bv -> PP.pretty "is (signed) greater than " <> signed w bv
    BVCmp L.Isge w bv -> PP.pretty "is (signed) greater than or equal to " <> signed w bv
  where
    signed :: forall ann w. (1 <= w) => NatRepr w -> BV w -> PP.Doc ann
    signed w bv =
      PP.viaShow (BV.asSigned w bv) PP.<+> PP.parens (PP.pretty (BV.ppHex w bv))
    unsigned :: forall ann w. (1 <= w) => NatRepr w -> BV w -> PP.Doc ann
    unsigned w bv =
      PP.viaShow (BV.asUnsigned bv) PP.<+> PP.parens (PP.pretty (BV.ppHex w bv))

-- | A \"relational\" constraint across several values.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data RelationalConstraint m (argTypes :: Ctx (FullType m))
  = -- | The first argument (a bitvector) is equal to the size of the allocation
    -- pointed to by the second.
    --
    -- @inTy@ and @inTy'@ are the overall types of the global variables or
    -- arguments to which this constraint applies. It's enforced that this
    -- constraint only applies to a value of integer type and a value of pointer
    -- type.
    forall inTy inTy' ft ft'.
    SizeOfAllocation
      (Selector m argTypes inTy ('FTInt ft))
      (Selector m argTypes inTy' ('FTPtr ft'))

--------------------------------------------------------------------------------

-- * Collections of constraints

data ConstrainedTypedValue m = forall ft.
  ConstrainedTypedValue
  { constrainedType :: FullTypeRepr m ft,
    constrainedValue :: ConstrainedShape m ft
  }

-- | A collection of constraints on the state of a program. These are used to
-- hold function preconditions deduced by
-- "UCCrux.LLVM.Classify.classifyBadBehavior".
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data Constraints m (argTypes :: Ctx (FullType m)) = Constraints
  { _argConstraints :: Ctx.Assignment (ConstrainedShape m) argTypes,
    _globalConstraints :: Map (GlobalSymbol m) (ConstrainedTypedValue m),
    _returnConstraints :: Map (FuncSymbol m) (ConstrainedTypedValue m),
    _relationalConstraints :: [RelationalConstraint m argTypes]
  }

argConstraints :: Simple Lens (Constraints m argTypes) (Ctx.Assignment (ConstrainedShape m) argTypes)
argConstraints = lens _argConstraints (\s v -> s {_argConstraints = v})

globalConstraints :: Simple Lens (Constraints m globalTypes) (Map (GlobalSymbol m) (ConstrainedTypedValue m))
globalConstraints = lens _globalConstraints (\s v -> s {_globalConstraints = v})

returnConstraints :: Simple Lens (Constraints m returnTypes) (Map (FuncSymbol m) (ConstrainedTypedValue m))
returnConstraints = lens _returnConstraints (\s v -> s {_returnConstraints = v})

relationalConstraints :: Simple Lens (Constraints m argTypes) [RelationalConstraint m argTypes]
relationalConstraints = lens _relationalConstraints (\s v -> s {_relationalConstraints = v})

-- | The minimal set of constraints on this 'Ctx.Assignment' of types. For each
-- input type, the generated 'ConstrainedShape' has the minimal memory footprint
-- (all pointers are not assumed to point to allocated memory) and an empty list
-- of 'Constraint'.
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

-- | The minimal set of constraints on a program state: no constraints
-- whatsoever on globals, and only the minimal constraints (see
-- 'emptyArgConstraints') on the function arguments.
emptyConstraints ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Constraints m argTypes
emptyConstraints argTypes =
  Constraints
    { _argConstraints = emptyArgConstraints argTypes,
      _globalConstraints = Map.empty,
      _returnConstraints = Map.empty,
      _relationalConstraints = []
    }

ppConstraints :: Constraints m argTypes -> Doc Void
ppConstraints (Constraints args globs returnCs relCs) =
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
          Just $
            nestSep
              ( PP.pretty "Globals:" :
                map (uncurry (ppLabeledValue getGlobalSymbol)) (Map.toList globs)
              ),
          Just $
            nestSep
              ( PP.pretty "Return values of skipped functions:" :
                map (uncurry (ppLabeledValue getFuncSymbol)) (Map.toList returnCs)
              ),
          -- These aren't yet generated anywhere
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

    ppLabeledValue getSymbol label (ConstrainedTypedValue _type (ConstrainedShape s)) =
      let L.Symbol nm = getSymbol label
       in PP.pretty nm
            <> PP.pretty ": "
            <> Shape.ppShape ppConstraints' s

isEmpty :: Constraints m argTypes -> Bool
isEmpty (Constraints args globs returns rels) =
  allFC isMin args
    && all (\(ConstrainedTypedValue _ s) -> isMin s) globs
    && null returns
    && null rels
  where
    isMin = Shape.isMinimal (null . getCompose) . getConstrainedShape

--------------------------------------------------------------------------------

-- * 'ConstrainedShape'

-- | A specification of the shape (memory layout) of a value and constraints on
-- it. See also the comment on 'Constraint'.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
newtype ConstrainedShape m (ft :: FullType m) = ConstrainedShape
  {getConstrainedShape :: Shape m (Compose [] (Constraint m)) ft}

minimalConstrainedShape :: FullTypeRepr m ft -> ConstrainedShape m ft
minimalConstrainedShape =
  ConstrainedShape . fmapFC (\_ -> Compose []) . Shape.minimal

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

-- | Given a 'ShapeConstraint' and a 'Shape', \"expand\" the shape by
-- transforming one of its embedded 'PtrShape' in one of three ways:
--
-- * Turn a 'ShapeUnallocated' into a 'ShapeAllocated'
-- * Turn a @'ShapeAllocated' n@ into a @'ShapeAllocated' m@ where @m > n@
-- * Turn a @'ShapeAllocated' n@ into a @'ShapeInitialized' m@ where @m >= n@
-- * Turn a @'ShapeInitialized' n@ into a @'ShapeInitialized' m@ where @m > n@
--
-- See the comment on 'ShapeConstraint' for where those are generated and how
-- this function is used.
expand ::
  forall m tag ft.
  ModuleTypes m ->
  (forall ft'. tag ft') ->
  FullTypeRepr m ft ->
  ShapeConstraint m ft ->
  Shape m tag ft ->
  (Maybe RedundantExpansion, Shape m tag ft)
expand mts minimalTag ftRepr shapeConstraint shape =
  let minimalSeq :: forall ft'. Int -> FullTypeRepr m ft' -> Seq (Shape m tag ft')
      minimalSeq sz ftr =
        Seq.replicate sz (fmapFC (const minimalTag) $ Shape.minimal ftr)
   in case (shapeConstraint, shape, ftRepr) of
        (Allocated n, Shape.ShapePtr tag Shape.ShapeUnallocated, FTPtrRepr {}) ->
          -- Create a new allocation
          (Nothing, Shape.ShapePtr tag (Shape.ShapeAllocated n))
        (Initialized n, Shape.ShapePtr tag Shape.ShapeUnallocated, FTPtrRepr ptRepr) ->
          -- Create and initialize a new allocation
          ( Nothing,
            Shape.ShapePtr
              tag
              (Shape.ShapeInitialized (minimalSeq n (asFullType mts ptRepr)))
          )
        (Initialized n, Shape.ShapePtr tag (Shape.ShapeAllocated m), FTPtrRepr ptRepr) ->
          ( Nothing,
            Shape.ShapePtr
              tag
              ( Shape.ShapeInitialized
                  (minimalSeq (max m n) (asFullType mts ptRepr))
              )
          )
        (Allocated n, Shape.ShapePtr tag (Shape.ShapeAllocated m), FTPtrRepr {}) ->
          if m >= n
            then (Just AllocateAllocated, shape) -- There's enough space already
            else -- Grow the allocation
              (Nothing, Shape.ShapePtr tag (Shape.ShapeAllocated n))
        (Allocated n, Shape.ShapePtr tag (Shape.ShapeInitialized vec), FTPtrRepr ptRepr) ->
          if Seq.length vec >= n
            then (Just AllocateInitialized, shape) -- There's enough space already
            else -- Grow the allocation

              ( Nothing,
                Shape.ShapePtr
                  tag
                  ( Shape.ShapeInitialized
                      (vec <> minimalSeq (n - Seq.length vec) (asFullType mts ptRepr))
                  )
              )
        (Initialized n, Shape.ShapePtr tag (Shape.ShapeInitialized vec), FTPtrRepr ptRepr) ->
          if Seq.length vec >= n
            then (Just InitializeInitialized, shape) -- There's enough space already
            else -- Grow the allocation

              ( Nothing,
                Shape.ShapePtr
                  tag
                  ( Shape.ShapeInitialized
                      (vec <> minimalSeq (n - Seq.length vec) (asFullType mts ptRepr))
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

-- | A constraint (precondition) learned by "UCCrux.LLVM.Classify" by simulating
-- a function.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data NewConstraint m (argTypes :: Ctx (FullType m))
  = forall atTy. NewShapeConstraint (SomeInSelector m argTypes atTy) (ShapeConstraint m atTy)
  | forall atTy. NewConstraint (SomeInSelector m argTypes atTy) (Constraint m atTy)
  | NewRelationalConstraint (RelationalConstraint m argTypes)

-- | Add a newly-deduced constraint to an existing set of constraints.
addConstraint ::
  forall m arch argTypes.
  ModuleContext m arch ->
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Constraints m argTypes ->
  NewConstraint m argTypes ->
  Either ExpansionError (Constraints m argTypes)
addConstraint modCtx argTypes constraints =
  \case
    NewConstraint (SomeInSelector (SelectGlobal symbol cursor)) constraint ->
      constraints & globalConstraints . atDefault symbol (newGlobalShape symbol)
        %%~ constrainTypedVal cursor (\_ftRepr -> addOneConstraint constraint)
    NewShapeConstraint (SomeInSelector (SelectGlobal symbol cursor)) shapeConstraint ->
      constraints & globalConstraints . atDefault symbol (newGlobalShape symbol)
        %%~ constrainTypedVal cursor (addOneShapeConstraint shapeConstraint)
    NewConstraint (SomeInSelector (SelectReturn symbol cursor)) constraint ->
      constraints & returnConstraints . atDefault symbol (newReturnValueShape symbol)
        %%~ constrainTypedVal cursor (\_ftRepr -> addOneConstraint constraint)
    NewShapeConstraint (SomeInSelector (SelectReturn symbol cursor)) shapeConstraint ->
      constraints & returnConstraints . atDefault symbol (newReturnValueShape symbol)
        %%~ constrainTypedVal cursor (addOneShapeConstraint shapeConstraint)
    NewConstraint (SomeInSelector (SelectArgument idx cursor)) constraint ->
      constraints & argConstraints . ixF' idx
        %%~ (\shape -> addOneConstraint constraint shape cursor)
    NewShapeConstraint (SomeInSelector (SelectArgument idx cursor)) shapeConstraint ->
      constraints & argConstraints . ixF' idx
        %%~ ( \shape ->
                addOneShapeConstraint shapeConstraint (argTypes ^. ixF' idx) shape cursor
            )
    NewRelationalConstraint relationalConstraint ->
      Right $ constraints & relationalConstraints %~ (relationalConstraint :)
    NewConstraint (SomeInSelector SelectClobbered {}) _ ->
      unimplemented "addConstraint" ClobberConstraints
    NewShapeConstraint (SomeInSelector SelectClobbered {}) _ ->
      unimplemented "addConstraint" ClobberConstraints
  where
    fromMaybeL :: forall a. a -> Lens.Lens' (Maybe a) a
    fromMaybeL def = lens (fromMaybe def) (\_old new -> Just new)

    atDefault ::
      forall c.
      Lens.At c =>
      Lens.Index c ->
      Lens.IxValue c ->
      Lens.Lens' c (Lens.IxValue c)
    atDefault idx def = at idx . fromMaybeL def
    
    addOneConstraint ::
      Constraint m atTy ->
      ConstrainedShape m ft ->
      Cursor m ft atTy ->
      Either ExpansionError (ConstrainedShape m ft)
    addOneConstraint constraint (ConstrainedShape shape) cursor =
      first
        ExpShapeSeekError
        (ConstrainedShape . fst <$> Shape.modifyTag (coerce (constraint :)) shape cursor)

    addOneShapeConstraint ::
      ShapeConstraint m atTy ->
      FullTypeRepr m inTy ->
      ConstrainedShape m inTy ->
      Cursor m inTy atTy ->
      Either ExpansionError (ConstrainedShape m inTy)
    addOneShapeConstraint shapeConstraint ft (ConstrainedShape shape) cursor =
      ConstrainedShape
        <$> joinLeft
          ExpShapeSeekError
          ( let doExpand shape' =
                  case expand
                    (modCtx ^. moduleTypes)
                    (Compose [])
                    (seekType (modCtx ^. moduleTypes) cursor ft)
                    shapeConstraint
                    shape' of
                    -- TODO(lb): Maybe warn here, there's a risk of an infinite
                    -- loop if there's a bug in classification.
                    (Just _redundant, result) -> Right result
                    (Nothing, result) -> Right result
             in Shape.modifyA' doExpand shape cursor
          )

    constrainTypedVal ::
      Cursor m inTy atTy ->
      ( forall ft.
        FullTypeRepr m ft ->
        ConstrainedShape m ft ->
        Cursor m ft atTy ->
        Either ExpansionError (ConstrainedShape m ft)
      ) ->
      ConstrainedTypedValue m ->
      Either ExpansionError (ConstrainedTypedValue m)
    constrainTypedVal cursor doAdd (ConstrainedTypedValue ft shape) =
      case checkCompatibility (modCtx ^. moduleTypes) cursor ft of
        Nothing -> panic "addConstraint" ["Ill-typed global or return value cursor"]
        Just cursor' -> ConstrainedTypedValue ft <$> doAdd ft shape cursor'

    newGlobalShape :: GlobalSymbol m -> ConstrainedTypedValue m
    newGlobalShape symbol =
      case modCtx ^. globalTypes . globalSymbol symbol of
        Some ft ->
          ConstrainedTypedValue
            ft
            (minimalConstrainedShape ft)

    newReturnValueShape :: FuncSymbol m -> ConstrainedTypedValue m
    newReturnValueShape symbol =
      case modCtx ^. funcTypes . funcSymbol symbol of
        Some (FuncSigRepr _ _ VoidRepr) ->
          panic
            "addConstraint"
            [ "Constraint on return value of void function: "
                ++ show (getFuncSymbol symbol)
            ]
        Some (FuncSigRepr _ _ (NonVoidRepr ft)) ->
          ConstrainedTypedValue ft (minimalConstrainedShape ft)
