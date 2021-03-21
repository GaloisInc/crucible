{-
Module           : UCCrux.LLVM.Cursor
Description      : A 'Cursor' points to a specific part of a function argument.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Cursor
  ( Cursor (..),
    ppCursor,

    -- * Operations on 'Cursor'
    findBottom,
    deepenPtr,
    deepenStruct,
    deepenArray,
    seekType,

    -- * 'Selector'
    Selector (..),
    SomeSelector (..),
    SomeInSelector (..),
    selectorCursor,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (Lens, lens, (^.))
import           Data.Semigroupoid (Semigroupoid(o))
import           Data.Void (Void)
import           Data.Type.Equality
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (OrdF(compareF), ixF')
import           Data.Parameterized.NatRepr (NatRepr, type (<=), type (+))
import qualified Data.Parameterized.TH.GADT as U

import           UCCrux.LLVM.FullType (FullType(..), FullTypeRepr(..))
import           UCCrux.LLVM.FullType.ModuleTypes (ModuleTypes)
import           UCCrux.LLVM.FullType.MemType (asFullType)
{- ORMOLU_ENABLE -}

-- | A 'Cursor' points to a specific part of a value (i.e. a function argument
-- or global variable). It's used for describing function preconditions, such as
-- \"@x->y@ must not be null\", or \"x[4] must be nonzero\".
--
-- The type variables are:
--
-- * @m@: The LLVM module where the 'FullType' being pointed into originates,
--   see also the comment on 'UCCrux.LLVM.FullType.CrucibleType.SomeAssign'.
-- * @inTy@: This is the \"outermost\" type, the type being pointed into.
-- * @atTy@: This is the \"innermost\" type, the type being pointed at.
data Cursor m (inTy :: FullType m) (atTy :: FullType m) where
  Here :: FullTypeRepr m atTy -> Cursor m atTy atTy
  Dereference ::
    -- | Which array index?
    Int ->
    Cursor m inTy atTy ->
    Cursor m ('FTPtr inTy) atTy
  Index ::
    (i + 1 <= n) =>
    -- | Which array index?
    NatRepr i ->
    -- | Overall array length.
    NatRepr n ->
    Cursor m inTy atTy ->
    Cursor m ('FTArray n inTy) atTy
  Field ::
    Ctx.Assignment (FullTypeRepr m) fields ->
    -- | Which field?
    Ctx.Index fields inTy ->
    Cursor m inTy atTy ->
    Cursor m ('FTStruct fields) atTy

instance Semigroupoid (Cursor m) where
  o cursor1 cursor2 =
    case (cursor1, cursor2) of
      (Here _, _) -> cursor2
      (_, Here _) -> cursor1
      (_, Field ftReprs idx cursor3) -> Field ftReprs idx (o cursor1 cursor3)
      (_, Index i n cursor3) -> Index i n (o cursor1 cursor3)
      (_, Dereference i cursor3) -> Dereference i (o cursor1 cursor3)

findBottom :: Cursor m inTy atTy -> FullTypeRepr m atTy
findBottom =
  \case
    Here repr -> repr
    Dereference _ cursor' -> findBottom cursor'
    Index _ _ cursor' -> findBottom cursor'
    Field _ _ cursor' -> findBottom cursor'

-- | If you've got enough type information on hand to determine that this
-- 'Cursor' points to a pointer type, you can get one that points to the
-- pointed-to type.
--
-- The resulting 'Cursor' points \"deeper\" into the top-level type.
deepenPtr ::
  ModuleTypes m ->
  Cursor m inTy ('FTPtr atTy) ->
  Cursor m inTy atTy
deepenPtr mts =
  \case
    Here (FTPtrRepr ptRepr) -> Dereference 0 (Here (asFullType mts ptRepr))
    Dereference i cursor -> Dereference i (deepenPtr mts cursor)
    Index i n cursor -> Index i n (deepenPtr mts cursor)
    Field fields idx cursor -> Field fields idx (deepenPtr mts cursor)

-- | Similarly to 'deepenPtr', if you know that a 'Cursor' points to a struct
-- and you know one of the fields of the struct, you can get a 'Cursor' that
-- points to that field.
deepenStruct ::
  Ctx.Index fields atTy ->
  Cursor m inTy ('FTStruct fields) ->
  Cursor m inTy atTy
deepenStruct idx =
  \case
    Here (FTStructRepr _structInfo fields) ->
      Field fields idx (Here (fields Ctx.! idx))
    Dereference i cursor -> Dereference i (deepenStruct idx cursor)
    Index i n cursor -> Index i n (deepenStruct idx cursor)
    Field fields idx' cursor -> Field fields idx' (deepenStruct idx cursor)

-- | Similarly to 'deepenPtr', if you know that a 'Cursor' points to an array
-- and you know the type contained in the array, you can get a 'Cursor' that
-- points to an element.
deepenArray ::
  (i + 1 <= n) =>
  NatRepr i ->
  NatRepr n ->
  Cursor m inTy ('FTArray n atTy) ->
  Cursor m inTy atTy
deepenArray idx len =
  \case
    Here (FTArrayRepr _n elems) ->
      Index idx len (Here elems)
    Dereference i cursor -> Dereference i (deepenArray idx len cursor)
    Index i n cursor -> Index i n (deepenArray idx len cursor)
    Field fields idx' cursor -> Field fields idx' (deepenArray idx len cursor)

-- | A 'Cursor' can be \"applied\" to a 'FullTypeRepr' to get a \"smaller\"
-- 'FullTypeRepr' that appears inside the \"outer\" one.
seekType ::
  ModuleTypes m ->
  Cursor m inTy atTy ->
  FullTypeRepr m inTy ->
  FullTypeRepr m atTy
seekType mts cursor ftRepr =
  case (cursor, ftRepr) of
    (Here _, _) -> ftRepr
    (Dereference _ rest, FTPtrRepr ptRepr) ->
      seekType mts rest (asFullType mts ptRepr)
    (Index _ _ rest, FTArrayRepr _ ftRepr') ->
      seekType mts rest ftRepr'
    (Field _ idx rest, FTStructRepr _ fields) ->
      seekType mts rest (fields ^. ixF' idx)

ppCursor ::
  -- | Top level, e.g. the name of a variable
  String ->
  Cursor m inTy atTy ->
  Doc Void
ppCursor top =
  \case
    Here _ft -> PP.pretty top
    Dereference 0 (Field _fieldTypes idx cursor) ->
      ppCursor top cursor <> PP.pretty "->" <> PP.pretty (show idx)
    Dereference 0 what -> PP.pretty "*" <> ppCursor top what
    Dereference idx what -> ppCursor top what <> PP.pretty ("[" ++ show idx ++ "]")
    Index idx _len cursor -> ppCursor top cursor <> PP.pretty ("[" ++ show idx ++ "]")
    Field _fieldTypes idx cursor ->
      ppCursor top cursor <> PP.pretty ("." ++ show idx)

-- | A 'Selector' points to a spot inside an argument or global variable.
--
-- For documentation of the type parameters, see the comment on 'Cursor'.
data Selector m (argTypes :: Ctx (FullType m)) inTy atTy
  = SelectArgument !(Ctx.Index argTypes inTy) (Cursor m inTy atTy)
  | SelectGlobal !L.Symbol (Cursor m inTy atTy)

-- | For documentation of the type parameters, see the comment on 'Cursor'.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data SomeSelector m (argTypes :: Ctx (FullType m))
  = forall inTy atTy. SomeSelector (Selector m argTypes inTy atTy)

-- | For documentation of the type parameters, see the comment on 'Cursor'.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data SomeInSelector m (argTypes :: Ctx (FullType m)) atTy
  = forall inTy. SomeInSelector (Selector m argTypes inTy atTy)

-- | Both kinds of 'Selector' (argument and global) contain a 'Cursor'.
selectorCursor ::
  Lens
    (Selector m argTypes inTy atTy)
    (Selector m argTypes inTy atTy')
    (Cursor m inTy atTy)
    (Cursor m inTy atTy')
selectorCursor =
  lens
    ( \case
        SelectArgument _ cursor -> cursor
        SelectGlobal _ cursor -> cursor
    )
    ( \s v ->
        case s of
          SelectArgument arg _ -> SelectArgument arg v
          SelectGlobal glob _ -> SelectGlobal glob v
    )

$(return [])

instance TestEquality (Cursor m inTy) where
  testEquality =
    $( U.structuralTypeEquality
         [t|Cursor|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|NatRepr|]),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|Cursor|]))),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Index|])),
                   [|testEquality|]
                 )
               ]
         )
     )

instance OrdF (Cursor m inTy) where
  compareF =
    $( U.structuralTypeOrd
         [t|Cursor|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|NatRepr|]),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|Cursor|]))),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Index|])),
                   [|compareF|]
                 )
               ]
         )
     )

instance TestEquality (Selector m argTypes inTy) where
  testEquality =
    $( U.structuralTypeEquality
         [t|Selector|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|NatRepr|]),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|Cursor|]))),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Index|])),
                   [|testEquality|]
                 )
               ]
         )
     )

instance OrdF (Selector m argTypes inTy) where
  compareF =
    $( U.structuralTypeOrd
         [t|Selector|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|NatRepr|]),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|Cursor|]))),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Index|])),
                   [|compareF|]
                 )
               ]
         )
     )
