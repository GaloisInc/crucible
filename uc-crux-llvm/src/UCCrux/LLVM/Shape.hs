{-
Module       : UCCrux.LLVM.Shape
Description  : The shapes of values
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module UCCrux.LLVM.Shape
  ( Shape (..),
    PtrShape (..),
    ShapeSeekError (..),
    ppShapeSeekError,
    ppShapeA,
    ppShape,
    eqShape,
    tag,
    modifyA,
    modifyA',
    modify,
    modify',
    modifyTag,
    getTag,
    setTag,
    minimal,
    isMinimal,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (Simple, Lens, lens, (^.), (.~))
import           Data.Coerce (coerce)
import           Data.Function ((&))
import           Data.Functor.Const (Const(Const, getConst))
import           Data.Functor.Identity (Identity(Identity))
import           Data.Kind (Type)
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as Vec
import           Data.Void (Void)
import           Data.Type.Equality ((:~:)(Refl))
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           Data.Parameterized.Classes (IxedF'(ixF'), EqF(eqF))
import           Data.Parameterized.NatRepr (NatRepr, decNat, minusPlusCancel, knownNat, natValue)
import           Data.Parameterized.Vector (Vector)
import qualified Data.Parameterized.Vector as PVec
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (FunctorFC(fmapFC), fmapFCDefault, TraversableFC(traverseFC), FoldableFC(foldMapFC), foldMapFCDefault, allFC)
import qualified Data.Parameterized.TH.GADT as U

import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.FullType.Type (FullType(..), FullTypeRepr(..))
{- ORMOLU_ENABLE -}

-- | A pointer can be unallocated (null-ish), allocated with a certain number of
-- elements, or allocated with a certain size and with certain parts
-- initialized/written.
--
-- For now, this type doesn\'t support partial initialization.
data PtrShape m tag ft
  = ShapeUnallocated
  | ShapeAllocated !Int
  | ShapeInitialized !(Vec.Vector (Shape m tag ft))

-- | A 'Shape' describes the layout of acyclic, non-aliasing values in memory
--
-- The functor @tag@ is for attaching annotations/tags.
data Shape (m :: Type) (tag :: FullType m -> Type) (ft :: FullType m) where
  ShapeInt ::
    tag ('FTInt n) ->
    -- NatRepr n ->
    Shape m tag ('FTInt n)
  ShapeFloat ::
    tag ('FTFloat flt) ->
    -- !(CrucibleTypes.FloatInfoRepr flt) ->
    Shape m tag ('FTFloat flt)
  ShapePtr ::
    tag ('FTPtr ft) ->
    PtrShape m tag ft ->
    Shape m tag ('FTPtr ft)
  -- | Function pointers don't have any sub-shapes because they aren't data
  -- pointers and can't be dereferenced.
  ShapeFuncPtr ::
    tag ('FTFuncPtr ret args) ->
    Shape m tag ('FTFuncPtr ret args)
  -- | Opaque pointers don't have any sub-shapes because they can't be
  -- dereferenced.
  ShapeOpaquePtr ::
    tag 'FTOpaquePtr ->
    Shape m tag 'FTOpaquePtr
  ShapeArray ::
    tag ('FTArray n ft) ->
    NatRepr n ->
    Vector n (Shape m tag ft) ->
    Shape m tag ('FTArray n ft)
  ShapeStruct ::
    tag ('FTStruct fields) ->
    Ctx.Assignment (Shape m tag) fields ->
    Shape m tag ('FTStruct fields)

ppShapeA ::
  Applicative
    f =>
  (forall ft'. tag ft' -> f (Doc Void)) ->
  Shape m tag ft ->
  f (Doc Void)
ppShapeA ppTag =
  \case
    ShapeInt tag' ->
      fmap (PP.pretty "An integer:" PP.<+>) (ppTag tag')
    ShapeFloat tag' ->
      fmap (PP.pretty "A float:" PP.<+>) (ppTag tag')
    ShapePtr tag' ShapeUnallocated ->
      fmap (PP.pretty "An unallocated/null(ish) pointer: " PP.<+>) (ppTag tag')
    ShapePtr tag' (ShapeAllocated n) ->
      fmap
        ( PP.hsep
            . ( [ PP.pretty "A pointer to uninitialized space for",
                  PP.viaShow n,
                  PP.pretty "elements:"
                ]
                  ++
              )
            . (: [])
        )
        (ppTag tag')
    ShapePtr tag' (ShapeInitialized v) ->
      -- TODO: Print elements
      fmap
        ( PP.hsep
            . ( [ PP.pretty "A pointer to initialized space for",
                  PP.viaShow (Vec.length v),
                  PP.pretty "elements:"
                ]
                  ++
              )
            . (: [])
        )
        (ppTag tag')
    ShapeFuncPtr tag' ->
      fmap (PP.pretty "A function pointer:" PP.<+>) (ppTag tag')
    ShapeOpaquePtr tag' ->
      fmap (PP.pretty "A pointer to an opaque type:" PP.<+>) (ppTag tag')
    ShapeArray tag' n _vec ->
      -- TODO print elements
      fmap
        ( PP.hsep
            . ( [ PP.pretty "An array of size",
                  PP.viaShow (natValue n) <> PP.pretty ":"
                ]
                  ++
              )
            . (: [])
        )
        (ppTag tag')
    ShapeStruct tag' _fields ->
      -- TODO print elements
      fmap
        ( PP.hsep
            . ( [ PP.pretty "A struct:"
                ]
                  ++
              )
            . (: [])
        )
        (ppTag tag')

ppShape ::
  (forall ft'. tag ft' -> Doc Void) ->
  Shape m tag ft ->
  Doc Void
ppShape ppTag = coerce (ppShapeA (Identity . ppTag))

eqShape ::
  (forall ft'. tag ft' -> tag ft' -> Bool) ->
  Shape m tag ft ->
  Shape m tag ft ->
  Bool
eqShape eqTag shape1 shape2 =
  case (shape1, shape2) of
    (ShapeInt tag1, ShapeInt tag2) -> eqTag tag1 tag2
    (ShapeFloat tag1, ShapeFloat tag2) -> eqTag tag1 tag2
    (ShapePtr tag1 ShapeUnallocated, ShapePtr tag2 ShapeUnallocated) -> eqTag tag1 tag2
    (ShapePtr tag1 (ShapeAllocated n1), ShapePtr tag2 (ShapeAllocated n2)) ->
      n1 == n2
        && eqTag tag1 tag2 -- O(1)
    (ShapePtr tag1 (ShapeInitialized rest1), ShapePtr tag2 (ShapeInitialized rest2)) ->
      Vec.length rest1 == Vec.length rest2
        && eqTag tag1 tag2 -- O(1)
        && all (uncurry (eqShape eqTag)) (Vec.zip rest1 rest2)
    (ShapeFuncPtr tag1, ShapeFuncPtr tag2) -> eqTag tag1 tag2
    (ShapeOpaquePtr tag1, ShapeOpaquePtr tag2) -> eqTag tag1 tag2
    (ShapeArray tag1 natRep1 rest1, ShapeArray tag2 natRep2 rest2) ->
      natValue natRep1 == natValue natRep2
        && eqTag tag1 tag2 -- O(1)
        && and (PVec.zipWith (eqShape eqTag) rest1 rest2)
    (ShapeStruct tag1 rest1, ShapeStruct tag2 rest2) ->
      eqTag tag1 tag2
        && allFC getConst (Ctx.zipWith (\s1 s2 -> Const (eqShape eqTag s1 s2)) rest1 rest2)
    (_, _) -> False

instance EqF tag => EqF (Shape m tag) where
  eqF = eqShape eqF

tag :: Simple Lens (Shape m tag ft) (tag ft)
tag =
  lens
    ( \case
        ShapeInt tg -> tg
        ShapeFloat tg -> tg
        ShapePtr tg _ -> tg
        ShapeFuncPtr tg -> tg
        ShapeOpaquePtr tg -> tg
        ShapeArray tg _ _ -> tg
        ShapeStruct tg _ -> tg
    )
    ( \s tg ->
        ( case s of
            ShapeInt _ -> ShapeInt tg
            ShapeFloat _ -> ShapeFloat tg
            ShapePtr _ rest -> ShapePtr tg rest
            ShapeFuncPtr _ -> ShapeFuncPtr tg
            ShapeOpaquePtr _ -> ShapeOpaquePtr tg
            ShapeArray _ n rest -> ShapeArray tg n rest
            ShapeStruct _ rest -> ShapeStruct tg rest
        )
    )

data ShapeSeekError
  = -- | First is index, second is size
    NotEnoughElements !Int !Int
  | DereferenceUnallocated
  | DereferenceUninitialized

ppShapeSeekError :: ShapeSeekError -> Text
ppShapeSeekError =
  Text.pack
    . \case
      NotEnoughElements _index _size -> "Not enough elements"
      DereferenceUnallocated -> "Dereference of unallocated memory"
      DereferenceUninitialized -> "Dereference of uninitialized memory"

-- How is this not a thing?
vUpdate :: Vec.Vector a -> Int -> a -> Vec.Vector a
vUpdate vec idx a = Vec.update vec (Vec.singleton (idx, a))

-- | Modify the 'Shape' at a given 'Cursor'
modifyA ::
  Functor f =>
  (Shape m tag atTy -> f (Shape m tag atTy, a)) ->
  Shape m tag inTy ->
  Cursor m inTy atTy ->
  Either ShapeSeekError (f (Shape m tag inTy, a))
modifyA f shape cursor =
  case (shape, cursor) of
    (_, Here _) -> Right (f shape)
    (ShapePtr _tag ShapeUnallocated, Dereference {}) -> Left DereferenceUnallocated
    (ShapePtr _tag ShapeAllocated {}, Dereference {}) -> Left DereferenceUninitialized
    (ShapePtr tag' (ShapeInitialized rest), Dereference i cursor') ->
      if i < Vec.length rest
        then
          modifyA f (rest Vec.! i) cursor'
            <&&> \(new, val) ->
              (ShapePtr tag' (ShapeInitialized (vUpdate rest i new)), val)
        else Left (NotEnoughElements i (Vec.length rest))
    (ShapeArray tag' sizeRepr rest, Index i _ cursor') ->
      modifyA f (PVec.elemAt i rest) cursor'
        <&&> \(new, val) -> (ShapeArray tag' sizeRepr (PVec.insertAt i new rest), val)
    (ShapeStruct tag' rest, Field _ idx cursor') ->
      modifyA f (rest Ctx.! idx) cursor'
        <&&> \(new, val) -> (ShapeStruct tag' (rest & ixF' idx .~ new), val)
  where
    x <&&> h = fmap (fmap h) x

-- | Modify the 'Shape' at a given 'Cursor'.
modifyA' ::
  Functor f =>
  (Shape m tag atTy -> f (Shape m tag atTy)) ->
  Shape m tag inTy ->
  Cursor m inTy atTy ->
  Either ShapeSeekError (f (Shape m tag inTy))
modifyA' f shape cursor = fmap fst <$> modifyA (fmap (,()) . f) shape cursor

-- | Modify a tag, returning the new value
modifyTag ::
  (tag atTy -> tag atTy) ->
  Shape m tag inTy ->
  Cursor m inTy atTy ->
  Either ShapeSeekError (Shape m tag inTy, tag atTy)
modifyTag f =
  modify
    ( \shape ->
        let newTag = f (shape ^. tag)
         in (shape & tag .~ newTag, newTag)
    )

-- | Modify the 'Shape' at a given 'Cursor', returning a computed value.
modify ::
  (Shape m tag atTy -> (Shape m tag atTy, a)) ->
  Shape m tag inTy ->
  Cursor m inTy atTy ->
  Either ShapeSeekError (Shape m tag inTy, a)
modify f shape cursor = coerce $ modifyA (Identity . f) shape cursor

-- | Modify the 'Shape' at a given 'Cursor'.
modify' ::
  (Shape m tag atTy -> Shape m tag atTy) ->
  Shape m tag inTy ->
  Cursor m inTy atTy ->
  Either ShapeSeekError (Shape m tag inTy)
modify' f shape cursor = coerce $ modifyA' (Identity . f) shape cursor

getTag :: Shape m tag inTy -> Cursor m inTy atTy -> Either ShapeSeekError (tag atTy)
getTag shape cursor = snd <$> modifyTag id shape cursor

setTag :: Shape m tag inTy -> Cursor m inTy atTy -> tag atTy -> Maybe ShapeSeekError
setTag shape cursor tag' =
  case modifyTag (const tag') shape cursor of
    Left err -> Just err
    Right _ -> Nothing

-- | Create the smallest 'Shape' of this type.
minimal :: FullTypeRepr m ft -> Shape m (Const ()) ft
minimal =
  \case
    FTIntRepr {} -> ShapeInt c
    FTFloatRepr {} -> ShapeFloat c
    FTPtrRepr {} -> ShapePtr c ShapeUnallocated
    FTVoidFuncPtrRepr {} -> ShapeFuncPtr c
    FTNonVoidFuncPtrRepr {} -> ShapeFuncPtr c
    FTOpaquePtrRepr {} -> ShapeOpaquePtr c
    FTArrayRepr n contained ->
      case minusPlusCancel n (knownNat :: NatRepr 1) of
        Refl -> ShapeArray c n (PVec.generate (decNat n) (\_ -> minimal contained))
    FTStructRepr _ fields -> ShapeStruct c (fmapFC minimal fields)
  where
    c = Const ()

-- | Property: @forall ftRepr. isMinimal (const True) (minimal ftRepr) == True@
isMinimal ::
  (forall ft'. tag ft' -> Bool) -> Shape m tag ft -> Bool
isMinimal isMinimalTag =
  \case
    ShapeInt tag' -> isMinimalTag tag'
    ShapeFloat tag' -> isMinimalTag tag'
    ShapePtr tag' ShapeUnallocated -> isMinimalTag tag'
    ShapePtr _tag' _ -> False
    ShapeFuncPtr tag' -> isMinimalTag tag'
    ShapeOpaquePtr tag' -> isMinimalTag tag'
    ShapeArray tag' _ rest -> isMinimalTag tag' && all (isMinimal isMinimalTag) rest
    ShapeStruct tag' rest -> isMinimalTag tag' && allFC (isMinimal isMinimalTag) rest

$(return [])

instance FunctorFC (Shape m) where
  fmapFC = fmapFCDefault

instance TraversableFC (Shape m) where
  traverseFC ::
    forall t f g h ft.
    Applicative h =>
    (forall x. f x -> h (g x)) ->
    Shape t f ft ->
    h (Shape t g ft)
  traverseFC =
    $( U.structuralTraversal
         [t|Shape|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (appAny (U.ConType [t|PtrShape|]))),
                   [|traverseFC|]
                 ),
                 ( appAny (appAny (U.ConType [t|Vector|])),
                   [|\(f :: forall x. f x -> h (g x)) -> traverse (traverseFC f)|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|\(f :: forall x. f x -> h (g x)) -> traverseFC (traverseFC f)|]
                 )
               ]
         )
     )

instance FoldableFC (Shape m) where
  foldMapFC = foldMapFCDefault

instance FunctorFC (PtrShape m) where
  fmapFC = fmapFCDefault

instance TraversableFC (PtrShape m) where
  traverseFC ::
    forall t f g h ft.
    Applicative h =>
    (forall x. f x -> h (g x)) ->
    PtrShape t f ft ->
    h (PtrShape t g ft)
  traverseFC =
    $( U.structuralTraversal
         [t|PtrShape|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|Vec.Vector|]),
                   [|\(f :: forall x. f x -> h (g x)) -> traverse (traverseFC f)|]
                 )
               ]
         )
     )

instance FoldableFC (PtrShape m) where
  foldMapFC = foldMapFCDefault
