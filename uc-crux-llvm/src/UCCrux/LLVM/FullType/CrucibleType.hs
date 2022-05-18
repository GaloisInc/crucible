{-
Module           : UCCrux.LLVM.FullType.CrucibleType
Description      : Interop between 'FullType' and 'CrucibleTypes.CrucibleType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.CrucibleType
  ( toCrucibleType,
    toCrucibleReturnType,

    -- * Assignments
    SomeIndex (..),
    SomeAssign' (..),
    assignmentToCrucibleType,
    assignmentToCrucibleTypeA,
    testCompatibility,
    testCompatibilityAssign,
    testCompatibilityReturn,
    translateIndex,
    generateM,
    generate,
    CrucibleTypeCompat(..),
    zip,

    -- * SameCrucibleType
    SameCrucibleType,
    sameCrucibleType,
    makeSameCrucibleType,
    sameCrucibleTypeRefl,
    MapSameCrucibleType,
    mapSameCrucibleType,
    mapSameCrucibleTypeRefl,
    testSameCrucibleType,
    testMapSameCrucibleType,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (unzip, zip, zipWith)

import           Data.Coerce (coerce)
import           Data.Functor ((<&>))
import           Data.Functor.Const (Const(Const))
import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Functor.Product (Product(Pair))

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

import           Crux.LLVM.Overrides (ArchOk)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.FuncSig (ReturnTypeRepr(..), ReturnTypeToCrucibleType)
import           UCCrux.LLVM.FullType.Type
{- ORMOLU_ENABLE -}

-- | c.f. @llvmTypeToRepr@
toCrucibleType ::
  ArchOk arch =>
  proxy arch ->
  FullTypeRepr m ft ->
  CrucibleTypes.TypeRepr (ToCrucibleType arch ft)
toCrucibleType proxy =
  \case
    FTIntRepr natRepr -> LLVMMem.LLVMPointerRepr natRepr
    FTPtrRepr {} -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTVoidFuncPtrRepr {} -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTNonVoidFuncPtrRepr {} -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTOpaquePtrRepr {} -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTFloatRepr floatInfo -> CrucibleTypes.FloatRepr floatInfo
    FTArrayRepr _natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType proxy fullTypeRepr)
    FTUnboundedArrayRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType proxy fullTypeRepr)
    FTStructRepr _ typeReprs ->
      case assignmentToCrucibleType proxy typeReprs of
        SomeAssign' ctReprs Refl _ -> CrucibleTypes.StructRepr ctReprs

toCrucibleReturnType ::
  ArchOk arch =>
  proxy arch ->
  ReturnTypeRepr m mft ->
  CrucibleTypes.TypeRepr (ReturnTypeToCrucibleType arch mft)
toCrucibleReturnType proxy =
  \case
    VoidRepr -> CrucibleTypes.UnitRepr
    NonVoidRepr ftRepr -> toCrucibleType proxy ftRepr

data SomeAssign' arch m fullTypes f = forall crucibleTypes.
  SomeAssign'
  { saCrucibleTypes :: Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes,
    saProof' :: MapToCrucibleType arch fullTypes :~: crucibleTypes,
    saValues :: Ctx.Assignment f crucibleTypes
  }

-- | Unzip an assignment of pairs into a pair of assignments.
--
-- TODO: This can be deleted and imported from parameterized-utils after its next
-- release following https://github.com/GaloisInc/parameterized-utils/pull/97.
unzip :: Ctx.Assignment (Product f g) ctx -> (Ctx.Assignment f ctx, Ctx.Assignment g ctx)
unzip fgs =
  case Ctx.viewAssign fgs of
    Ctx.AssignEmpty -> (Ctx.empty, Ctx.empty)
    Ctx.AssignExtend rest (Pair f g) ->
      let (fs, gs) = unzip rest
       in (Ctx.extend fs f, Ctx.extend gs g)

-- | Convert from a 'Ctx.Assignment' of 'FullTypeRepr' to a 'Ctx.Assignment' of
-- 'CrucibleTypes.TypeRepr', together with a proof of the correspondence of the
-- two assignments via 'MapToCrucibleType'.
assignmentToCrucibleTypeA ::
  (Applicative f, ArchOk arch) =>
  proxy arch ->
  (forall ft. Ctx.Index fts ft -> FullTypeRepr m ft -> f (g (ToCrucibleType arch ft))) ->
  Ctx.Assignment (FullTypeRepr m) fts ->
  f (SomeAssign' arch m fts g)
assignmentToCrucibleTypeA proxy g fullTypes =
  let someCrucibleTypes =
        Ctx.generateSomeM
          (Ctx.sizeInt (Ctx.size fullTypes))
          ( \idx ->
              case Ctx.intIndex idx (Ctx.size fullTypes) of
                Nothing ->
                  panic
                    "assignmentToCrucibleTypeA"
                    ["Impossible: Index was from the same context!"]
                Just (Some idx') ->
                  let ft = fullTypes Ctx.! idx'
                   in g idx' ft <&> \val -> Some (Pair val (toCrucibleType proxy ft))
          )
   in someCrucibleTypes
        <&> \(Some both) ->
          let (values, crucibleTypes) = unzip both
           in case testCompatibilityAssign proxy fullTypes crucibleTypes of
                Just Refl -> SomeAssign' crucibleTypes Refl values
                Nothing ->
                  panic
                    "assignmentToCrucibleTypeA"
                    ["Impossible: Types match by construction!"]

assignmentToCrucibleType ::
  ArchOk arch =>
  proxy arch ->
  Ctx.Assignment (FullTypeRepr m) fts ->
  SomeAssign' arch m fts (Const ())
assignmentToCrucibleType proxy fullTypes =
  runIdentity
    (assignmentToCrucibleTypeA proxy (\_ _ -> Identity (Const ())) fullTypes)

testCompatibility ::
  forall proxy arch m ft tp.
  ArchOk arch =>
  proxy arch ->
  FullTypeRepr m ft ->
  CrucibleTypes.TypeRepr tp ->
  Maybe (ToCrucibleType arch ft :~: tp)
testCompatibility proxy fullTypeRepr = testEquality (toCrucibleType proxy fullTypeRepr)

testCompatibilityAssign ::
  ArchOk arch =>
  proxy arch ->
  Ctx.Assignment (FullTypeRepr m) ctx1 ->
  Ctx.Assignment CrucibleTypes.TypeRepr ctx2 ->
  Maybe (MapToCrucibleType arch ctx1 :~: ctx2)
testCompatibilityAssign proxy ftAssign ctAssign =
  case (Ctx.viewAssign ftAssign, Ctx.viewAssign ctAssign) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Just Refl
    (Ctx.AssignExtend ftRest ftHead, Ctx.AssignExtend ctRest ctHead) ->
      case (testCompatibility proxy ftHead ctHead, testCompatibilityAssign proxy ftRest ctRest) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    _ -> Nothing

-- | Test compatibility of a 'ReturnTypeRepr' against a 'CrucibleTypes.TypeRepr'.
--
-- Crucible represents LLVM functions with a @void@ return type as returning
-- @Unit@. This corresponds to a 'VoidRepr' in 'ReturnTypeRepr'. Non-unit
-- Crucible types are tested for compatibility (using 'testCompatibility')
-- against the content of the 'NonVoidRepr'.
testCompatibilityReturn ::
  ArchOk arch =>
  proxy arch ->
  ReturnTypeRepr m mft ->
  -- | Crucible representative of a function return type
  CrucibleTypes.TypeRepr cty ->
  Maybe (ReturnTypeToCrucibleType arch mft :~: cty)
testCompatibilityReturn proxy rty cty =
  case (cty, rty) of
    (CrucibleTypes.UnitRepr, VoidRepr) -> Just Refl
    (_, VoidRepr) -> Nothing
    (CrucibleTypes.UnitRepr, NonVoidRepr _) -> Nothing
    (_, NonVoidRepr fty) ->
      case testCompatibility proxy fty cty of
        Just Refl -> Just Refl
        Nothing -> Nothing

data SomeIndex arch ft crucibleTypes
  = forall tp. SomeIndex (Ctx.Index crucibleTypes tp) (ToCrucibleType arch ft :~: tp)

translateSize ::
  proxy arch ->
  Ctx.Size fullTypes ->
  Ctx.Size (MapToCrucibleType arch fullTypes)
translateSize proxy sz =
  case Ctx.viewSize sz of
    Ctx.ZeroSize -> Ctx.zeroSize
    Ctx.IncSize sz' -> Ctx.incSize (translateSize proxy sz')

translateIndex ::
  proxy arch ->
  Ctx.Size fullTypes ->
  Ctx.Index fullTypes ft ->
  SomeIndex arch ft (MapToCrucibleType arch fullTypes)
translateIndex proxy sz idx =
  case (Ctx.viewSize sz, Ctx.viewIndex sz idx) of
    (Ctx.IncSize _, Ctx.IndexViewLast sz') ->
      SomeIndex (Ctx.lastIndex (Ctx.incSize (translateSize proxy sz'))) Refl
    (Ctx.IncSize sz', Ctx.IndexViewInit idx') ->
      case translateIndex proxy sz' idx' of
        SomeIndex idx'' Refl -> SomeIndex (Ctx.skipIndex idx'') Refl
    (Ctx.ZeroSize, _) ->
      panic
        "translateIndex"
        ["Impossible: Can't index into empty/zero-size context."]

-- | c.f. 'Ctx.generateM'
generateM ::
  Applicative m =>
  proxy arch ->
  Ctx.Size fullTypes ->
  ( forall ft tp.
    Ctx.Index fullTypes ft ->
    Ctx.Index (MapToCrucibleType arch fullTypes) tp ->
    (ToCrucibleType arch ft :~: tp) ->
    m (f tp)
  ) ->
  m (Ctx.Assignment f (MapToCrucibleType arch fullTypes))
generateM proxy sz f =
  case Ctx.viewSize sz of
    Ctx.ZeroSize -> pure Ctx.empty
    Ctx.IncSize sz' ->
      Ctx.extend
        <$> generateM
          proxy
          sz'
          (\idx idx' Refl -> f (Ctx.skipIndex idx) (Ctx.skipIndex idx') Refl)
        <*> case translateIndex proxy sz (Ctx.lastIndex sz) of
          SomeIndex idx' Refl -> f (Ctx.lastIndex sz) idx' Refl

-- | c.f. 'Ctx.generate'
generate ::
  proxy arch ->
  Ctx.Size fullTypes ->
  ( forall ft tp.
    Ctx.Index fullTypes ft ->
    Ctx.Index (MapToCrucibleType arch fullTypes) tp ->
    (ToCrucibleType arch ft :~: tp) ->
    f tp
  ) ->
  Ctx.Assignment f (MapToCrucibleType arch fullTypes)
generate proxy sz f = coerce (generateM proxy sz (\i1 i2 refl -> Identity (f i1 i2 refl)))

-- | Re-index a type that is indexed by Crucible types to be indexed by
-- 'FullType' instead. Useful when you want to maintain information about the
-- compatibility between data over Crucible types and 'FullType', see 'zip'.
newtype CrucibleTypeCompat arch f ft =
  CrucibleTypeCompat (f (ToCrucibleType arch ft))

zipWith ::
  ArchOk arch =>
  proxy arch ->
  (forall ft. f ft -> g (ToCrucibleType arch ft) -> h ft) ->
  Ctx.Assignment f ctx ->
  Ctx.Assignment g (MapToCrucibleType arch ctx) ->
  Ctx.Assignment h ctx
zipWith proxy fun ftAssign ctAssign =
  case (Ctx.viewAssign ftAssign, Ctx.viewAssign ctAssign) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) -> Ctx.empty
    (Ctx.AssignExtend ftRest ftHead, Ctx.AssignExtend ctRest ctHead) ->
      Ctx.extend (zipWith proxy fun ftRest ctRest) (fun ftHead ctHead)

-- | Zip an assignment over 'FullType' with a compatible assignment over
-- Crucible types, maintaining the type-level correspondence via
-- 'CrucibleTypeCompat'.
zip ::
  ArchOk arch =>
  proxy arch ->
  Ctx.Assignment f ctx ->
  Ctx.Assignment g (MapToCrucibleType arch ctx) ->
  Ctx.Assignment (Product f (CrucibleTypeCompat arch g)) ctx
zip proxy = zipWith proxy (\ft ct -> Pair ft (CrucibleTypeCompat ct))

-- ------------------------------------------------------------------------------
-- SameCrucibleType

-- | A proof that two 'FullType's map to the same Crucible type, in any
-- architecture.
newtype SameCrucibleType ft ft' =
  SameCrucibleType
    { getSameCrucibleType ::
      forall proxy arch.
      proxy arch ->
      ToCrucibleType arch ft :~: ToCrucibleType arch ft'
    }

sameCrucibleType ::
  SameCrucibleType ft ft' ->
  proxy arch ->
  ToCrucibleType arch ft :~: ToCrucibleType arch ft'
sameCrucibleType (SameCrucibleType prf) arch = prf arch

makeSameCrucibleType ::
  (forall proxy arch. proxy arch -> ToCrucibleType arch ft :~: ToCrucibleType arch ft') ->
  SameCrucibleType ft ft'
makeSameCrucibleType = SameCrucibleType

sameCrucibleTypeRefl :: SameCrucibleType ft ft
sameCrucibleTypeRefl = SameCrucibleType (\_arch -> Refl)

-- | A proof that two contexts of 'FullType's map to the same contexts of
-- Crucible types, in any architecture.
newtype MapSameCrucibleType ctx ctx' =
  MapSameCrucibleType
    { getMapSameCrucibleType ::
      forall proxy arch.
      proxy arch ->
      MapToCrucibleType arch ctx :~: MapToCrucibleType arch ctx'
    }

mapSameCrucibleType ::
  MapSameCrucibleType ctx ctx' ->
  proxy arch ->
  MapToCrucibleType arch ctx :~: MapToCrucibleType arch ctx'
mapSameCrucibleType (MapSameCrucibleType prf) arch = prf arch

mapSameCrucibleTypeRefl :: MapSameCrucibleType ctx ctx
mapSameCrucibleTypeRefl = MapSameCrucibleType (\_arch -> Refl)

testMapSameCrucibleType ::
  Ctx.Assignment (FullTypeRepr m) ctx ->
  Ctx.Assignment (FullTypeRepr m) ctx' ->
  Maybe (MapSameCrucibleType ctx ctx')
testMapSameCrucibleType a a' =
  case (Ctx.viewAssign a, Ctx.viewAssign a') of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) ->
      Just (MapSameCrucibleType (\_arch -> Refl))
    (Ctx.AssignExtend rest hd, Ctx.AssignExtend rest' hd') ->
      case (testSameCrucibleType hd hd', testMapSameCrucibleType rest rest') of
        (Just prf1, Just prf2) ->
          Just $ MapSameCrucibleType $ \arch ->
            case (sameCrucibleType prf1 arch, mapSameCrucibleType prf2 arch) of
              (Refl, Refl) -> Refl
        _ -> Nothing
    _ -> Nothing

-- | Check if two 'FullTypeRepr's are the same up to pointers.
testSameCrucibleType ::
  FullTypeRepr m ft ->
  FullTypeRepr m ft' ->
  Maybe (SameCrucibleType ft ft')
testSameCrucibleType ft ft' =
  case (ft, ft') of
    (FTIntRepr natRepr, FTIntRepr natRepr') ->
      do Refl <- testEquality natRepr natRepr'
         return (SameCrucibleType (\_arch -> Refl))
    (FTPtrRepr{}, FTPtrRepr{}) -> Just (SameCrucibleType (\_arch -> Refl))
    (FTFloatRepr fi, FTFloatRepr fi') ->
      do Refl <- testEquality fi fi'
         return (SameCrucibleType (\_arch -> Refl))
    (FTVoidFuncPtrRepr{}, FTVoidFuncPtrRepr{}) ->
      Just (SameCrucibleType (\_arch -> Refl))
    (FTNonVoidFuncPtrRepr{}, FTNonVoidFuncPtrRepr{}) ->
      Just (SameCrucibleType (\_arch -> Refl))
    (FTOpaquePtrRepr nm, FTOpaquePtrRepr nm') ->
      do Refl <- testEquality nm nm'
         return (SameCrucibleType (\_arch -> Refl))
    (FTArrayRepr natRepr itemRepr, FTArrayRepr natRepr' itemRepr') ->
      do Refl <- testEquality natRepr natRepr'
         subPrf <- testSameCrucibleType itemRepr itemRepr'
         return $ SameCrucibleType $ \arch ->
           case sameCrucibleType subPrf arch of
             Refl -> Refl
    (FTUnboundedArrayRepr itemRepr, FTUnboundedArrayRepr itemRepr') ->
      do subPrf <- testSameCrucibleType itemRepr itemRepr'
         return $ SameCrucibleType $ \arch ->
           case sameCrucibleType subPrf arch of
             Refl -> Refl
    (FTStructRepr sp fields, FTStructRepr sp' fields') ->
      do subPrf <- testMapSameCrucibleType fields fields'
         Refl <- testEquality sp sp'
         return $ SameCrucibleType $ \arch ->
           case mapSameCrucibleType subPrf arch of
             Refl -> Refl
    _ -> Nothing
