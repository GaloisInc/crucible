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
{-# LANGUAGE FlexibleContexts #-}
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
    PartTypeRepr, -- Constructor hidden for safety of unsafeCoerce below
    MapToCrucibleType,
    ToCrucibleType,
    MapToBaseType,
    ToBaseType,
    isPtrRepr,
    IsPtrRepr (..),
    aliasOrFullType,
    toPartType,

    -- * Opaque pointers
    OpaquePointers,
    MapOpaquePointers,
    testOpaquePointers,
    testMapOpaquePointers,

    -- * Translation
    toFullType,
    toFullTypeM,

    -- * 'ModuleTypes'
    ModuleTypes,
    TypeLookupResult (..),
    ModuleAndTypes(..),
    makeModuleTypes,
    lookupType,
    processingType,
    finishedType,

    -- * Lookup
    asFullType',
    asFullType,
    pointedToType,
    arrayElementType,
  )
where

{- ORMOLU_DISABLE -}
import           GHC.TypeLits (Nat)
import           Data.Functor.Identity (Identity(runIdentity))
import           Control.Monad.Except (MonadError, runExceptT)
import           Control.Monad.State (MonadState, runStateT, get, modify)
import           Data.Kind (Type)
import           Data.Functor.Const (Const(Const))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (isJust)
import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import qualified Data.Vector as Vec
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.Classes (OrdF(compareF), OrderingF(LTF, GTF, EQF))
import           Data.Parameterized.NatRepr (NatRepr, type (<=), mkNatRepr, isPosNat, LeqProof(..))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TH.GADT as U

import qualified Text.LLVM.AST as L

import qualified What4.InterpretedFloatingPoint as W4IFP

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType, lookupAlias)

import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVMArch)
import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..), FunDecl(..))
import qualified Lang.Crucible.LLVM.MemType as MemType

import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.Module (Module, makeSomeModule)
import           UCCrux.LLVM.FullType.VarArgs
{- ORMOLU_ENABLE -}

-- | Type level only.
--
-- The @m@ parameter represents an LLVM module, see comment on
-- 'UCCrux.LLVM.FullType.CrucibleType.TranslatedTypes'.
data FullType (m :: Type) where
  FTInt :: Nat -> FullType m
  FTPtr :: FullType m -> FullType m
  FTFloat :: CrucibleTypes.FloatInfo -> FullType m
  -- | The 'Maybe' here captures the C pattern of an dynamically-sized array
  -- within a struct. See test/programs/unsized_array.c.
  FTArray :: Maybe Nat -> FullType m -> FullType m
  FTStruct :: Ctx.Ctx (FullType m) -> FullType m
  -- | Function pointers are very different from data pointers - they don't
  -- contain any data and can't be dereferenced. By treating function pointers
  -- \"as a whole\" (rather than having function types themselves by a
  -- constructor of 'FullType'), we can retain more totality/definedness in
  -- functions like @toFullType@.
  FTFuncPtr :: IsVarArgs -> Maybe (FullType m) -> Ctx.Ctx (FullType m) -> FullType m
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
  ToCrucibleType arch ('FTFuncPtr _varArgs _ret _args) =
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
    FullTypeRepr m ('FTArray ('Just n) ft)
  FTUnboundedArrayRepr ::
    FullTypeRepr m ft ->
    FullTypeRepr m ('FTArray 'Nothing ft)
  FTStructRepr ::
    MemType.StructInfo ->
    Ctx.Assignment (FullTypeRepr m) fields ->
    FullTypeRepr m ('FTStruct fields)
  FTVoidFuncPtrRepr ::
    VarArgsRepr varArgs ->
    Ctx.Assignment (FullTypeRepr m) args ->
    FullTypeRepr m ('FTFuncPtr varArgs 'Nothing args)
  FTNonVoidFuncPtrRepr ::
    VarArgsRepr varArgs ->
    FullTypeRepr m ret ->
    Ctx.Assignment (FullTypeRepr m) args ->
    FullTypeRepr m ('FTFuncPtr varArgs ('Just ret) args)
  -- TODO(lb): This could have a symbol repr for the name
  FTOpaquePtrRepr :: L.Ident -> FullTypeRepr m 'FTOpaquePtr

-- | This functions similarly to 'MemType.SymType'
data PartTypeRepr (m :: Type) (ft :: FullType m) where
  PTFullRepr :: FullTypeRepr m ft -> PartTypeRepr m ft
  -- The Const is so that we can get type variables in scope in the TestEquality
  -- instance, see below.
  PTAliasRepr :: Const L.Ident ft -> PartTypeRepr m ft

-- ------------------------------------------------------------------------------
-- Opaque pointers

-- | Make all pointer types opaque.
--
-- Useful for ensuring two 'FullType's will map to the same Crucible type,
-- without requiring a specification of the architecture (an @arch@ variable),
-- see 'UCCrux.LLVM.FullType.CrucibleType.opaquePointersToCrucibleCompat'.
type family OpaquePointers (ft :: FullType m) :: FullType m where
  OpaquePointers ('FTPtr _) = 'FTOpaquePtr
  OpaquePointers ('FTFuncPtr _ _ _) = 'FTOpaquePtr
  OpaquePointers ('FTArray n elems) = 'FTArray n (OpaquePointers elems)
  OpaquePointers ('FTStruct fields) = 'FTStruct (MapOpaquePointers fields)
  OpaquePointers ft = ft

type family MapOpaquePointers (ctx :: Ctx (FullType m)) :: Ctx (FullType m) where
  MapOpaquePointers 'Ctx.EmptyCtx = 'Ctx.EmptyCtx
  MapOpaquePointers (xs 'Ctx.::> x) =
    MapOpaquePointers xs Ctx.::> OpaquePointers x

-- | Check if two 'Ctx.Assignment's of 'FullTypeRepr's are the same up to pointers.
testMapOpaquePointers ::
  Ctx.Assignment (FullTypeRepr m) ctx ->
  Ctx.Assignment (FullTypeRepr m) ctx' ->
  Maybe (MapOpaquePointers ctx :~: MapOpaquePointers ctx')
testMapOpaquePointers a a' =
  case (Ctx.viewAssign a, Ctx.viewAssign a') of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Just Refl
    (Ctx.AssignExtend rest hd, Ctx.AssignExtend rest' hd') ->
      case (testOpaquePointers hd hd', testMapOpaquePointers rest rest') of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    _ -> Nothing

-- | Check if two 'FullTypeRepr's are the same up to pointers.
testOpaquePointers ::
  FullTypeRepr m ft ->
  FullTypeRepr m ft' ->
  Maybe (OpaquePointers ft :~: OpaquePointers ft')
testOpaquePointers ft ft' =
  case (ft, ft') of
    (FTIntRepr natRepr, FTIntRepr natRepr') ->
      case testEquality natRepr natRepr' of
        Nothing -> Nothing
        Just Refl -> Just Refl
    (FTPtrRepr{}, FTPtrRepr{}) -> Just Refl
    (FTFloatRepr fi, FTFloatRepr fi') ->
      case testEquality fi fi' of
        Nothing -> Nothing
        Just Refl -> Just Refl
    (FTVoidFuncPtrRepr{}, FTVoidFuncPtrRepr{}) -> Just Refl
    (FTNonVoidFuncPtrRepr{}, FTNonVoidFuncPtrRepr{}) -> Just Refl
    (FTOpaquePtrRepr{}, FTOpaquePtrRepr{}) -> Just Refl
    (FTArrayRepr natRepr itemRepr, FTArrayRepr natRepr' itemRepr') ->
      case (testEquality natRepr natRepr', testOpaquePointers itemRepr itemRepr') of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (FTUnboundedArrayRepr itemRepr, FTUnboundedArrayRepr itemRepr') ->
      case testOpaquePointers itemRepr itemRepr' of
        Just Refl -> Just Refl
        Nothing -> Nothing
    (FTStructRepr _ fields, FTStructRepr _ fields') ->
      case testMapOpaquePointers fields fields' of
        Just Refl -> Just Refl
        Nothing -> Nothing
    _ -> Nothing

-- ------------------------------------------------------------------------------
-- Instances

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
                 ( appAny (U.ConType [t|VarArgsRepr|]),
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
                 ( appAny (U.ConType [t|VarArgsRepr|]),
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

instance Eq (FullTypeRepr m ft) where
  ft1 == ft2 = isJust (testEquality ft1 ft2)

aliasOrFullType :: PartTypeRepr m ft -> Either L.Ident (FullTypeRepr m ft)
aliasOrFullType =
  \case
    PTFullRepr ft -> Right ft
    PTAliasRepr (Const ident) -> Left ident

data IsPtrRepr m ft = forall ft'. IsPtrRepr (ft :~: 'FTPtr ft')

toPartType :: FullTypeRepr m ft -> PartTypeRepr m ft
toPartType = PTFullRepr

isPtrRepr :: forall m ft. FullTypeRepr m ft -> Maybe (IsPtrRepr m ft)
isPtrRepr =
  \case
    FTPtrRepr _ -> Just (IsPtrRepr Refl)
    _ -> Nothing

-- ------------------------------------------------------------------------------
-- Translation

data AsMemType
  = WasOpaque
  | WasFun
  | WasVoid
  | WasUnsupported
  | AsMemType MemType

asMemType' :: (?lc :: TypeContext) => String -> Either L.Ident MemType
asMemType' strIdent =
  case helper (Alias (L.Ident strIdent)) of
    Left _ ->
      panic
        "asMemType''"
        [ "Couldn't find declaration for type alias:",
          strIdent,
          "Possibly a bug in Clang?"
        ]
    Right WasOpaque -> Left (L.Ident strIdent)
    Right WasUnsupported -> unimplemented "toFullTypeM" Unimplemented.UnsupportedType
    Right WasVoid ->
      panic "toFullTypeM" ["Type alias was alias of void: ", strIdent]
    Right WasFun ->
      -- Is this possible in LLVM? Haven't run into it yet.
      panic "toFullTypeM" ["Type alias was alias of function type: ", strIdent]
    Right (AsMemType mt') -> Right mt'
  where
    -- c.f. 'asMemType'
    helper :: (?lc :: TypeContext, MonadError String m) => SymType -> m AsMemType
    helper (MemType mt) = return (AsMemType mt)
    helper (Alias i) = helper =<< lookupAlias i
    helper OpaqueType = return WasOpaque
    helper FunType {} = return WasFun
    helper VoidType = return WasVoid
    helper UnsupportedType {} = return WasUnsupported

toFullTypeM ::
  forall m f.
  ( MonadState (ModuleTypes m) f,
    MonadError L.Ident f
  ) =>
  MemType ->
  f (Some (FullTypeRepr m))
toFullTypeM memType =
  case memType of
    PtrType (MemType memType') ->
      do
        Some pointedTo <- toFullTypeM memType'
        pure $ Some (FTPtrRepr (PTFullRepr pointedTo))
    -- This case is crucial for safety: We have to store the resulting looked-up
    -- type in the ModuleTypes so that we can look it up in asFullType.
    PtrType (Alias ident@(L.Ident strIdent)) ->
      do
        mts <- get
        let result = Some (FTPtrRepr (PTAliasRepr (Const ident)))
        case lookupType mts ident of
          Found _ ->
            -- We've already processed this type, it's safe, move on.
            pure result
          Processing ->
            -- We're processing a recursive circle of types In this case, it's
            -- safe to *not* store the type because our caller will. In fact we
            -- must not try to calculate it for the sake of termination.
            pure result
          Missing ->
            -- We haven't yet encountered this type
            do
              modify (flip processingType ident)
              let ?lc = typeContext mts
              Some ftRepr <-
                case asMemType' strIdent of
                  Left opaqueIdent -> pure $ Some (FTOpaquePtrRepr opaqueIdent)
                  Right mt -> toFullTypeM mt
              modify (\mts' -> finishedType mts' ident (Some ftRepr))
              pure result
    IntType w ->
      case mkNatRepr w of
        Some w' | Just LeqProof <- isPosNat w' -> pure (Some (FTIntRepr w'))
        _ -> panic "toPartType" ["Invalid integer width " ++ show w]
    VecType n memType' ->
      do
        Some contained <- toFullTypeM memType'
        Some natRepr <- pure $ mkNatRepr n
        case isPosNat natRepr of
          Just LeqProof -> pure (Some (FTArrayRepr natRepr contained))
          Nothing -> panic "toPartType" ["Zero vector type size"]
    StructType structInfo ->
      do
        let structInfoFields = MemType.siFields structInfo
        Some fields <-
          Ctx.generateSomeM
            (length structInfoFields)
            ( \idx -> toFullTypeM (MemType.fiType (structInfoFields Vec.! idx))
            )
        pure (Some (FTStructRepr structInfo fields))
    PtrType (FunType (FunDecl retType argTypes isVarArgs)) ->
      do
        Some argTypeReprs <-
          Ctx.generateSomeM
            (length argTypes)
            (\idx -> toFullTypeM (argTypes !! idx))
        Some varArgsRepr <- pure $ boolToVarArgsRepr isVarArgs
        case retType of
          Just retType' ->
            do
              Some retTypeRepr <- toFullTypeM retType'
              pure (Some (FTNonVoidFuncPtrRepr varArgsRepr retTypeRepr argTypeReprs))
          Nothing -> pure (Some (FTVoidFuncPtrRepr varArgsRepr argTypeReprs))
    FloatType -> pure (Some (FTFloatRepr W4IFP.SingleFloatRepr))
    DoubleType -> pure (Some (FTFloatRepr W4IFP.DoubleFloatRepr))
    X86_FP80Type -> pure (Some (FTFloatRepr W4IFP.X86_80FloatRepr))
    ArrayType size content ->
      do
        Some sizeRepr <- pure $ mkNatRepr size
        Some contentRepr <- toFullTypeM content
        case isPosNat sizeRepr of
          Just LeqProof -> pure (Some (FTArrayRepr sizeRepr contentRepr))
          Nothing -> pure (Some (FTUnboundedArrayRepr contentRepr))
    PtrType OpaqueType {} ->
      panic "toFullType" ["Pointer to opaque type without type alias?"]
    PtrType UnsupportedType {} -> unimplemented "toFullType" Unimplemented.UnsupportedType
    -- These ones should maybe cause a panic?
    PtrType VoidType {} -> unimplemented "toFullType" Unimplemented.VoidType
    MetadataType {} -> unimplemented "toFullType" Unimplemented.MetadataType

toFullType ::
  forall m.
  ModuleTypes m ->
  MemType ->
  (Either L.Ident (Some (FullTypeRepr m)), ModuleTypes m)
toFullType moduleTypes memType =
  runIdentity $ runStateT (runExceptT (toFullTypeM memType)) moduleTypes

-- ------------------------------------------------------------------------------
-- ModuleTypes

-- | The @m@ parameter represents an LLVM module, see comment on
-- "UCCrux.LLVM.Module".
data ModuleTypes (m :: Type) = ModuleTypes
  { typeContext :: TypeContext,
    fullTypes :: Map L.Ident (Maybe (Some (FullTypeRepr m)))
  }

-- | The @m@ parameter represents an LLVM module, see comment on
-- "UCCrux.LLVM.Module".
data TypeLookupResult m
  = forall ft. Found (FullTypeRepr m ft)
  | Processing
  | Missing

-- | The existentially-quantified @m@ parameter represents an LLVM module, see
-- comment on "UCCrux.LLVM.Module".
data ModuleAndTypes =
  forall m.
  ModuleAndTypes
    { moduleAndTypesModule :: Module m,
      moduleAndTypesTypes :: ModuleTypes m
    }

-- | Take a module and its corresponding 'TypeContext', and reify their
-- relationship via a phantom type parameter @m@. Precondition: This
-- 'TypeContext' corresponds to this module.
makeModuleTypes :: L.Module -> TypeContext -> ModuleAndTypes
makeModuleTypes m tc =
  case makeSomeModule m of
    Some m' -> ModuleAndTypes m' (ModuleTypes tc Map.empty)

lookupType :: ModuleTypes m -> L.Ident -> TypeLookupResult m
lookupType mts ident =
  case Map.lookup ident (fullTypes mts) of
    Nothing -> Missing
    (Just (Just (Some ty))) -> Found ty
    (Just Nothing) -> Processing

finishedType :: ModuleTypes m -> L.Ident -> Some (FullTypeRepr m) -> ModuleTypes m
finishedType (ModuleTypes tc fts) ident ty =
  ModuleTypes tc (Map.insert ident (Just ty) fts)

processingType :: ModuleTypes m -> L.Ident -> ModuleTypes m
processingType (ModuleTypes tc fts) ident =
  ModuleTypes tc (Map.insert ident Nothing fts)

-- ------------------------------------------------------------------------------
-- Lookup

-- | c.f. @asMemType@
asFullType' ::
  ModuleTypes m ->
  PartTypeRepr m ft ->
  Either L.Ident (FullTypeRepr m ft)
asFullType' mts =
  \case
    PTFullRepr fullRepr -> Right fullRepr
    PTAliasRepr (Const ident) ->
      let ?lc = typeContext mts
       in case asMemType (MemType.Alias ident) of
            Left _err -> Left ident
            Right memType ->
              case toFullType mts memType of
                (Left err, _) -> Left err
                (Right (Some ft), _) ->
                  -- This is safe because of what happens in the Alias case of
                  -- toFullTypeM, namely we check that the alias was properly
                  -- translated in this module. See comment on
                  -- 'UCCrux.LLVM.FullType.CrucibleType.SomeAssign'.
                  Right (unsafeCoerce ft)

asFullType ::
  ModuleTypes m ->
  PartTypeRepr m ft ->
  FullTypeRepr m ft
asFullType mts ptRepr =
  case asFullType' mts ptRepr of
    Right ok -> ok
    Left _err ->
      case ptRepr of
        PTAliasRepr (Const (L.Ident name)) ->
          -- See comment on 'UCCrux.LLVM.FullType.CrucibleType.SomeAssign'.
          panic
            "asFullType"
            ["Impossible: couldn't find definition for type alias: " <> name]
        _ -> panic "asFullType" ["Impossible case"]

pointedToType ::
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  FullTypeRepr m ft
pointedToType mts (FTPtrRepr ptRepr) = asFullType mts ptRepr

arrayElementType ::
  FullTypeRepr m ('FTArray sz ft) ->
  FullTypeRepr m ft
arrayElementType =
  \case
    FTArrayRepr _ subRepr -> subRepr
    FTUnboundedArrayRepr subRepr -> subRepr
