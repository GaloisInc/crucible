{-
Module           : UCCrux.LLVM.FullType.Type
Description      : 'FullType' is like a 'CrucibleTypes.CrucibleType' and a 'MemType.MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

A 'FullType' is like a 'CrucibleTypes.CrucibleType', but contains type
information through pointer references. Alternatively, it\'s like a
'MemType.MemType' that can be linked to a 'CrucibleTypes.CrucibleType' by
type-level information.

Using this machinery, heads off several sources of partiality/errors:

* By passing a 'FullType' instead of a 'MemType.MemType' and a
  'CrucibleTypes.CrucibleType', it becomes impossible to pass
  incompatible/out-of-sync inputs.
* When building a @RegValue@, using 'FullType' can help prevent ill-typed
  pointers, or instances of metadata or @void@ appearing in invalid places.
* There are a few sources of partiality in the 'MemType.MemType' to
  'CrucibleTypes.TypeRepr' translation that can be avoided, specifically
  ill-sized integer values.
* 'FullType' distinguishes between pointers and pointer-widths integers.
* 'FullType' distinguishes between code pointers and data pointers.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-inaccessible-code #-}
-- These come from TH-generated code
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module UCCrux.LLVM.FullType.Type
  ( type FullType (..),
    FullTypeRepr (..),
    PartTypeRepr (..),
    MapToCrucibleType,
    ToCrucibleType,
    MapToBaseType,
    ToBaseType,
    isPtrRepr,
    IsPtrRepr (..),
  )
where

{- ORMOLU_DISABLE -}
import           GHC.TypeLits (Nat)
import           Data.Kind (Type)
import           Data.Functor.Const (Const(Const))
import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.Classes (OrdF(compareF), OrderingF(LTF, GTF, EQF))
import           Data.Parameterized.NatRepr (NatRepr, type (<=))
import qualified Data.Parameterized.TH.GADT as U

import qualified Text.LLVM.AST as L

import qualified What4.InterpretedFloatingPoint as W4IFP

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVMArch)
import qualified Lang.Crucible.LLVM.MemType as MemType
{- ORMOLU_ENABLE -}

-- | Type level only.
--
-- The @m@ parameter represents an LLVM module, see comment on
-- 'UCCrux.LLVM.FullType.CrucibleType.SomeAssign'.
data FullType (m :: Type) where
  FTInt :: Nat -> FullType m
  FTPtr :: FullType m -> FullType m
  FTFloat :: CrucibleTypes.FloatInfo -> FullType m
  FTArray :: Nat -> FullType m -> FullType m
  FTStruct :: Ctx.Ctx (FullType m) -> FullType m
  -- | Function pointers are very different from data pointers - they don't
  -- contain any data and can't be dereferenced. By treating function pointers
  -- \"as a whole\" (rather than having function types themselves by a
  -- constructor of 'FullType'), we can retain more totality/definedness in
  -- functions like @toFullType@.
  FTFuncPtr :: Maybe (FullType m) -> Ctx.Ctx (FullType m) -> FullType m
  -- | Similarly to function pointers, pointers to opaque struct types can't be
  -- dereferenced.
  FTOpaquePtr :: FullType m

type family MapToCrucibleType arch (ctx :: Ctx (FullType m)) :: Ctx CrucibleTypes.CrucibleType where
  MapToCrucibleType arch 'Ctx.EmptyCtx = Ctx.EmptyCtx
  MapToCrucibleType arch (xs 'Ctx.::> x) = MapToCrucibleType arch xs Ctx.::> ToCrucibleType arch x

type family ToCrucibleType arch (ft :: FullType m) :: CrucibleTypes.CrucibleType where
  ToCrucibleType arch ('FTInt n) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType n)
  ToCrucibleType arch ('FTPtr _ft) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))
  ToCrucibleType arch ('FTFloat flt) = CrucibleTypes.FloatType flt
  ToCrucibleType arch ('FTArray _n ft) =
    CrucibleTypes.VectorType (ToCrucibleType arch ft)
  ToCrucibleType arch ('FTStruct ctx) =
    CrucibleTypes.StructType (MapToCrucibleType arch ctx)
  ToCrucibleType arch ('FTFuncPtr ret args) =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))
  ToCrucibleType arch 'FTOpaquePtr =
    CrucibleTypes.IntrinsicType
      "LLVM_pointer"
      (Ctx.EmptyCtx Ctx.::> CrucibleTypes.BVType (ArchWidth arch))

type family MapToBaseType (sym :: Type) (arch :: LLVMArch) (ctx :: Ctx (FullType m)) :: Ctx CrucibleTypes.BaseType where
  MapToBaseType sym arch 'Ctx.EmptyCtx = Ctx.EmptyCtx
  MapToBaseType sym arch (xs 'Ctx.::> x) =
    MapToBaseType sym arch xs Ctx.::> ToBaseType sym arch x

-- | The type of annotated What4 values that correspond to each 'FullType'
type family ToBaseType (sym :: Type) (arch :: LLVMArch) (ft :: FullType m) :: CrucibleTypes.BaseType where
  ToBaseType sym arch ('FTInt n) = CrucibleTypes.BaseBVType n
  ToBaseType sym arch ('FTPtr _ft) = CrucibleTypes.BaseIntegerType
  ToBaseType sym arch ('FTFloat flt) = W4IFP.SymInterpretedFloatType sym flt
  ToBaseType sym arch ('FTStruct ctx) =
    CrucibleTypes.BaseStructType (MapToBaseType sym arch ctx)

data FullTypeRepr (m :: Type) (ft :: FullType m) where
  FTIntRepr ::
    (1 <= w) =>
    !(NatRepr w) ->
    FullTypeRepr m ('FTInt w)
  FTPtrRepr ::
    PartTypeRepr m ft ->
    FullTypeRepr m ('FTPtr ft)
  FTFloatRepr ::
    !(CrucibleTypes.FloatInfoRepr flt) ->
    FullTypeRepr m ('FTFloat flt)
  FTArrayRepr ::
    (1 <= n) =>
    !(NatRepr n) ->
    FullTypeRepr m ft ->
    FullTypeRepr m ('FTArray n ft)
  FTStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment (FullTypeRepr m) fields ->
    FullTypeRepr m ('FTStruct fields)
  FTVoidFuncPtrRepr ::
    Ctx.Assignment (FullTypeRepr m) args ->
    FullTypeRepr m ('FTFuncPtr 'Nothing args)
  FTNonVoidFuncPtrRepr ::
    FullTypeRepr m ret ->
    Ctx.Assignment (FullTypeRepr m) args ->
    FullTypeRepr m ('FTFuncPtr ('Just ret) args)
  -- TODO(lb): This could have a symbol repr for the name
  FTOpaquePtrRepr :: L.Ident -> FullTypeRepr m 'FTOpaquePtr

-- | This functions similarly to 'MemType.SymType'
data PartTypeRepr (m :: Type) (ft :: FullType m) where
  PTFullRepr :: FullTypeRepr m ft -> PartTypeRepr m ft
  -- The Const is so that we can get type variables in scope in the TestEquality
  -- instance, see below.
  PTAliasRepr :: Const L.Ident ft -> PartTypeRepr m ft

data IsPtrRepr m ft = forall ft'. IsPtrRepr (ft :~: 'FTPtr ft')

isPtrRepr :: forall m ft. FullTypeRepr m ft -> Maybe (IsPtrRepr m ft)
isPtrRepr =
  \case
    FTPtrRepr _ -> Just (IsPtrRepr Refl)
    _ -> Nothing

$(return [])

-- | We assume (via unsafeCoerce) that types with the same L.Ident are the same.
-- This is validated by the existential used in @makeModuleTypes@.
instance TestEquality (PartTypeRepr m) where
  testEquality =
    $( U.structuralTypeEquality
         [t|PartTypeRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|testEquality|]
                 ),
                 ( appAny (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|])),
                   [|
                     \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                       if ident1 == ident2 then Just (unsafeCoerce Refl :: ft1 :~: ft2) else Nothing
                     |]
                 )
               ]
         )
     )

instance TestEquality (FullTypeRepr m) where
  testEquality =
    $( U.structuralTypeEquality
         [t|FullTypeRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|NatRepr|]),
                   [|testEquality|]
                 ),
                 ( appAny (U.ConType [t|CrucibleTypes.FloatInfoRepr|]),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|PartTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|testEquality|]
                 )
               ]
         )
     )

-- | See note on 'TestEquality' instance.
instance OrdF (PartTypeRepr m) where
  compareF =
    $( U.structuralTypeOrd
         [t|PartTypeRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|compareF|]
                 ),
                 ( appAny (U.TypeApp (U.ConType [t|Const|]) (U.ConType [t|L.Ident|])),
                   [|
                     \(Const ident1 :: Const L.Ident ft1) (Const ident2 :: Const L.Ident ft2) ->
                       case compare ident1 ident2 of
                         LT -> unsafeCoerce LTF :: OrderingF ft1 ft2
                         GT -> unsafeCoerce GTF :: OrderingF ft1 ft2
                         EQ -> unsafeCoerce EQF :: OrderingF ft1 ft2
                     |]
                 )
               ]
         )
     )

instance OrdF (FullTypeRepr m) where
  compareF =
    $( U.structuralTypeOrd
         [t|FullTypeRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|NatRepr|]),
                   [|compareF|]
                 ),
                 ( appAny (U.ConType [t|CrucibleTypes.FloatInfoRepr|]),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|PartTypeRepr|])),
                   [|compareF|]
                 )
               ]
         )
     )
