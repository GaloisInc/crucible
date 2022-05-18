{-
Module       : UCCrux.LLVM.Precondition
Description  : LLVM function preconditions
Copyright    : (c) Galois, Inc 2022
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
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module UCCrux.LLVM.Precondition
  ( Preconds (..),
    argPreconds,
    globalPreconds,
    postconds,
    relationalPreconds,
    emptyPreconds,
    ppPreconds,
    isEmpty,

    -- * Expansion
    expand,
    ExpansionError (..),
    ppExpansionError,

    -- * 'NewConstraint'
    NewConstraint (..),
    addPrecond,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (Simple, Lens, lens, (%~), (%%~), (^.), at)
import qualified Control.Lens as Lens
import           Data.Bifunctor (first)
import           Data.Coerce (coerce)
import           Data.Function ((&))
import           Data.Functor.Compose (Compose(..))
import           Data.Maybe (catMaybes, fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void as Void
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.Classes (IxedF'(ixF'))
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC (allFC, fmapFC, toListFC)

import           UCCrux.LLVM.Context.Module (ModuleContext, funcTypes, globalTypes, moduleTypes)
import           UCCrux.LLVM.Constraints (Constraint, ConstrainedShape(..), ConstrainedTypedValue(..), RelationalConstraint, ShapeConstraint (Allocated, Initialized), ppConstraint, minimalConstrainedShape)
import           UCCrux.LLVM.Cursor (Cursor, Selector(..), SomeInSelector(SomeInSelector), seekType, checkCompatibility)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(ClobberPreconds))
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Shape (Shape, ShapeSeekError)
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr(FuncSigRepr), ReturnTypeRepr(VoidRepr, NonVoidRepr))
import           UCCrux.LLVM.FullType.Type (FullType(..), FullTypeRepr(FTPtrRepr), ModuleTypes, asFullType)
import           UCCrux.LLVM.Module (GlobalSymbol, globalSymbol, getGlobalSymbol, FuncSymbol, funcSymbol, getFuncSymbol)
import           UCCrux.LLVM.Postcondition.Type (UPostcond)
import qualified UCCrux.LLVM.Postcondition.Type as Post
{- ORMOLU_ENABLE -}

-- | A collection of constraints on the state of a program. These are used to
-- hold function preconditions deduced by
-- "UCCrux.LLVM.Classify.classifyBadBehavior".
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data Preconds m (argTypes :: Ctx (FullType m)) = Preconds
  { _argPreconds :: Ctx.Assignment (ConstrainedShape m) argTypes,
    _globalPreconds :: Map (GlobalSymbol m) (ConstrainedTypedValue m),
    _postconds :: Map (FuncSymbol m) (UPostcond m),
    _relationalPreconds :: [RelationalConstraint m argTypes]
  }

argPreconds :: Simple Lens (Preconds m argTypes) (Ctx.Assignment (ConstrainedShape m) argTypes)
argPreconds = lens _argPreconds (\s v -> s {_argPreconds = v})

globalPreconds :: Simple Lens (Preconds m globalTypes) (Map (GlobalSymbol m) (ConstrainedTypedValue m))
globalPreconds = lens _globalPreconds (\s v -> s {_globalPreconds = v})

postconds :: Simple Lens (Preconds m returnTypes) (Map (FuncSymbol m) (UPostcond m))
postconds = lens _postconds (\s v -> s {_postconds = v})

relationalPreconds :: Simple Lens (Preconds m argTypes) [RelationalConstraint m argTypes]
relationalPreconds = lens _relationalPreconds (\s v -> s {_relationalPreconds = v})

-- | The minimal set of constraints on this 'Ctx.Assignment' of types. For each
-- input type, the generated 'ConstrainedShape' has the minimal memory footprint
-- (all pointers are not assumed to point to allocated memory) and an empty list
-- of 'Constraint'.
emptyArgPreconds ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Ctx.Assignment (ConstrainedShape m) argTypes
emptyArgPreconds argTypes =
  fmapFC
    ( \argType ->
        ConstrainedShape
          (fmapFC (\_ -> Compose []) $ Shape.minimal argType)
    )
    argTypes

-- | The minimal set of constraints on a program state: no constraints
-- whatsoever on globals, and only the minimal constraints (see
-- 'emptyArgPreconds') on the function arguments.
emptyPreconds ::
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Preconds m argTypes
emptyPreconds argTypes =
  Preconds
    { _argPreconds = emptyArgPreconds argTypes,
      _globalPreconds = Map.empty,
      _postconds = Map.empty,
      _relationalPreconds = []
    }

ppPreconds :: Preconds m argTypes -> Doc Void
ppPreconds (Preconds args globs posts relCs) =
  PP.vsep
    ( catMaybes
        [ if Ctx.sizeInt (Ctx.size args) == 0
            then Nothing
            else
              Just $
                nestSep
                  ( PP.pretty "Arguments:" :
                    toListFC
                      (Shape.ppShape ppPreconds' . getConstrainedShape)
                      args
                  ),
          Just $
            nestSep
              ( PP.pretty "Globals:" :
                map (uncurry (ppLabeledValue getGlobalSymbol)) (Map.toList globs)
              ),
          Just $
            nestSep
              ( PP.pretty "Postconditions of skipped functions:" :
                map (uncurry (ppLabeled getFuncSymbol Post.ppUPostcond)) (Map.toList posts)
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
    ppPreconds' (Compose constraints) = PP.vsep (map ppConstraint constraints)
    nestSep = PP.nest 2 . PP.vsep

    ppLabeledValue getSymbol label (ConstrainedTypedValue _type (ConstrainedShape s)) =
      ppLabeled getSymbol (Shape.ppShape ppPreconds') label s

    ppLabeled getSymbol f label val =
      let L.Symbol nm = getSymbol label
       in PP.pretty nm <> PP.pretty ": " <> f val

isEmpty :: Preconds m argTypes -> Bool
isEmpty (Preconds args globs returns rels) =
  allFC isMin args
    && all (\(ConstrainedTypedValue _ s) -> isMin s) globs
    && null returns
    && null rels
  where
    isMin = Shape.isMinimal (null . getCompose) . getConstrainedShape

--------------------------------------------------------------------------------

-- * Expansion

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

data ExpansionError
  = ExpRedundant RedundantExpansion
  | ExpShapeSeekError ShapeSeekError

ppExpansionError :: ExpansionError -> Text
ppExpansionError =
  \case
    ExpRedundant redundant -> ppRedundantExpansion redundant
    ExpShapeSeekError ssErr -> Shape.ppShapeSeekError ssErr

--------------------------------------------------------------------------------

-- * 'NewConstraint'

-- | A constraint (precondition) learned by "UCCrux.LLVM.Classify" by simulating
-- a function.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data NewConstraint m (argTypes :: Ctx (FullType m))
  = forall atTy. NewShapeConstraint (SomeInSelector m argTypes atTy) (ShapeConstraint m atTy)
  | forall atTy. NewConstraint (SomeInSelector m argTypes atTy) (Constraint m atTy)
  | NewRelationalConstraint (RelationalConstraint m argTypes)

-- | Add a newly-deduced constraint to an existing set of preconditions.
addPrecond ::
  forall m arch argTypes.
  ModuleContext m arch ->
  Ctx.Assignment (FullTypeRepr m) argTypes ->
  Preconds m argTypes ->
  NewConstraint m argTypes ->
  Either ExpansionError (Preconds m argTypes)
addPrecond modCtx argTypes constraints =
  \case
    NewConstraint (SomeInSelector (SelectGlobal symbol cursor)) constraint ->
      constraints & globalPreconds . atDefault symbol (newGlobalShape symbol)
        %%~ constrainTypedVal cursor (\_ftRepr -> addOneConstraint constraint)
    NewShapeConstraint (SomeInSelector (SelectGlobal symbol cursor)) shapeConstraint ->
      constraints & globalPreconds . atDefault symbol (newGlobalShape symbol)
        %%~ constrainTypedVal cursor (addOneShapeConstraint shapeConstraint)
    NewConstraint (SomeInSelector (SelectReturn symbol cursor)) constraint ->
      constraints &
        postconds
        . atDefault symbol Post.emptyUPostcond
        . Post.uReturnValue
        . fromMaybeL (newReturnValueShape symbol)
        %%~ constrainTypedVal cursor (\_ftRepr -> addOneConstraint constraint)
    NewShapeConstraint (SomeInSelector (SelectReturn symbol cursor)) shapeConstraint ->
      constraints &
        postconds
        . atDefault symbol Post.emptyUPostcond
        . Post.uReturnValue
        . fromMaybeL (newReturnValueShape symbol)
        %%~ constrainTypedVal cursor (addOneShapeConstraint shapeConstraint)
    NewConstraint (SomeInSelector (SelectArgument idx cursor)) constraint ->
      constraints & argPreconds . ixF' idx
        %%~ (\shape -> addOneConstraint constraint shape cursor)
    NewShapeConstraint (SomeInSelector (SelectArgument idx cursor)) shapeConstraint ->
      constraints & argPreconds . ixF' idx
        %%~ ( \shape ->
                addOneShapeConstraint shapeConstraint (argTypes ^. ixF' idx) shape cursor
            )
    NewRelationalConstraint relationalConstraint ->
      Right $ constraints & relationalPreconds %~ (relationalConstraint :)
    NewConstraint (SomeInSelector SelectClobbered {}) _ ->
      unimplemented "addPrecond" ClobberPreconds
    NewShapeConstraint (SomeInSelector SelectClobbered {}) _ ->
      unimplemented "addPrecond" ClobberPreconds
  where
    -- Examples:
    --
    -- >>> Nothing & fromMaybeL 5 %~ (+1)
    -- Just 6
    -- >>> Just 0 & fromMaybeL 7 %~ (+1)
    -- Just 1
    fromMaybeL :: forall a. a -> Lens.Lens' (Maybe a) a
    fromMaybeL def = lens (fromMaybe def) (\_old new -> Just new)

    -- Examples:
    --
    -- >>> Map.fromList [(0, ""), (1, "-")] & atDefault 2 "!" %~ (++ ".")
    -- fromList [(0,""),(1,"-"),(2,"!.")]
    -- >>> Map.fromList [(0, ""), (1, "-")] & atDefault 1 "!" %~ (++ ".")
    -- fromList [(0,""),(1,"-.")]
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
        Nothing -> panic "addPrecond" ["Ill-typed global or return value cursor"]
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
        Some (FuncSigRepr _ _ (NonVoidRepr ft)) ->
          ConstrainedTypedValue ft (minimalConstrainedShape ft)
        Some (FuncSigRepr _ _ VoidRepr) ->
          panic
            "addPrecond"
            [ "Constraint on return value of void function: "
                ++ show (getFuncSymbol symbol)
            ]
