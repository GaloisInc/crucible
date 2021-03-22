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

    -- * Assignments
    SomeAssign (..),
    SomeIndex (..),
    assignmentToFullType,
    SomeAssign' (..),
    assignmentToCrucibleType,
    assignmentToCrucibleTypeA,
    translateIndex,
    generateM,
    generate,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (unzip)

import           Data.Coerce (coerce)
import           Data.Functor ((<&>))
import           Data.Functor.Const (Const(Const, getConst))
import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Functor.Product (Product(Pair))
import           Control.Monad.State (runStateT)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (MemType(..))
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Crux.LLVM.Overrides (ArchOk)
import           UCCrux.LLVM.Errors.Panic (panic)
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
    FTPtrRepr _ -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTVoidFuncPtrRepr _argTypeReprs -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTNonVoidFuncPtrRepr _retTypeRepr _argTypeReprs -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTOpaquePtrRepr _aliasName -> LLVMMem.LLVMPointerRepr ?ptrWidth
    FTFloatRepr floatInfo -> CrucibleTypes.FloatRepr floatInfo
    FTArrayRepr _natRepr fullTypeRepr ->
      CrucibleTypes.VectorRepr (toCrucibleType proxy fullTypeRepr)
    FTStructRepr _ typeReprs ->
      case assignmentToCrucibleType proxy typeReprs of
        SomeAssign' ctReprs Refl _ -> CrucibleTypes.StructRepr ctReprs

-- | The existential quantification over @m@ here makes the @FullType@ API safe.
-- You can only intermingle 'FullTypeRepr' from the same LLVM module, and by
-- construction, the 'ModuleTypes' contains a 'FullTypeRepr' for every type
-- that\'s (transitively) mentioned in any of the types in the 'Ctx.Assignment'.
-- Thus, you can avoid partiality when looking up type aliases in the
-- 'ModuleTypes', they're guaranteed to be present and translated.
--
-- See 'UCCrux.LLVM.FullType.MemType.asFullType' for where partiality is
-- avoided. Since this function is ubiquitous, this is a big win.
data SomeAssign arch crucibleTypes = forall m fullTypes.
  SomeAssign
  { saFullTypes :: Ctx.Assignment (FullTypeRepr m) fullTypes,
    saModuleTypes :: ModuleTypes m,
    saProof :: MapToCrucibleType arch fullTypes :~: crucibleTypes
  }

-- | Convert from a 'Ctx.Assignment' of 'CrucibleTypes.TypeRepr' to a
-- 'Ctx.Assignment' of 'FullTypeRepr', together with a proof of the
-- correspondence of the two assignments via 'MapToCrucibleType'.
assignmentToFullType ::
  forall proxy arch crucibleTypes.
  ( ?lc :: TypeContext,
    ArchOk arch
  ) =>
  proxy arch ->
  Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes ->
  Ctx.Assignment (Const MemType) crucibleTypes ->
  Either L.Ident (SomeAssign arch crucibleTypes)
assignmentToFullType proxy crucibleTypes memTypes =
  case makeModuleTypes ?lc of
    Some moduleTypes ->
      do
        (Some fullTypes, moduleTypes') <-
          runStateT
            ( Ctx.generateSomeM
                (Ctx.sizeInt (Ctx.size crucibleTypes))
                ( \idx ->
                    case Ctx.intIndex idx (Ctx.size crucibleTypes) of
                      Nothing -> panic "Impossible" ["Mismatched context size"]
                      Just (Some idx') ->
                        do
                          Some fullTypeRepr <-
                            toFullTypeM (getConst (memTypes Ctx.! idx'))
                          pure $ Some fullTypeRepr
                )
            )
            moduleTypes
        case testCompatibilityAssign proxy fullTypes crucibleTypes of
          Just Refl -> Right (SomeAssign fullTypes moduleTypes' Refl)
          Nothing -> panic "Impossible" []

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
