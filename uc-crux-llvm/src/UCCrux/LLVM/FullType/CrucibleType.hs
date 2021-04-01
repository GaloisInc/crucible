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

    -- * Translation
    FunctionTypes (..),
    MatchingAssign (..),
    DeclTypes,
    TranslatedTypes (..),
    TypeTranslationError (..),
    isDebug,
    translateModuleDefines,
    ppTypeTranslationError,
    lookupDeclTypes,

    -- * Assignments
    SomeIndex (..),
    SomeAssign' (..),
    assignmentToCrucibleType,
    assignmentToCrucibleTypeA,
    testCompatibility,
    testCompatibilityAssign,
    translateIndex,
    generateM,
    generate,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (unzip)

import           Control.Monad (unless)
import           Control.Monad.Except (ExceptT, runExceptT, throwError, withExceptT)
import           Control.Monad.State (State, runState)
import           Data.Coerce (coerce)
import           Data.Functor ((<&>))
import           Data.Functor.Const (Const(Const))
import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Functor.Product (Product(Pair))
import qualified Data.List as List
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (fdArgTypes, fdRetType, fdVarArgs)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Crux.LLVM.Overrides (ArchOk)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.Type
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr, boolToVarArgsRepr)
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

data FunctionTypes m arch = FunctionTypes
  { ftArgTypes :: MatchingAssign m arch,
    ftRetType :: Maybe (Some (FullTypeRepr m)),
    ftIsVarArgs :: Some VarArgsRepr
  }

data MatchingAssign m arch = forall fullTypes crucibleTypes.
  MapToCrucibleType arch fullTypes ~ crucibleTypes =>
  MatchingAssign
  { maFullTypes :: Ctx.Assignment (FullTypeRepr m) fullTypes,
    maCrucibleTypes :: Ctx.Assignment CrucibleTypes.TypeRepr crucibleTypes
  }

-- | Constructor not exported to enforce the invariant that a 'DeclTypes' holds
-- a 'FunctionTypes' for every LLVM function in the corresponding module
-- indicated by the @m@ parameter.
newtype DeclTypes m arch = DeclTypes {_getDeclTypes :: Map L.Symbol (FunctionTypes m arch)}

lookupDeclTypes :: L.Symbol -> DeclTypes m arch -> Maybe (FunctionTypes m arch)
lookupDeclTypes symb (DeclTypes mp) = Map.lookup symb mp

-- | The existential quantification over @m@ here makes the @FullType@ API safe.
-- You can only intermingle 'FullTypeRepr' from the same LLVM module, and by
-- construction, the 'ModuleTypes' contains a 'FullTypeRepr' for every type
-- that\'s (transitively) mentioned in any of the types in the 'DeclTypes'.
-- Thus, you can avoid partiality when looking up type aliases in the
-- 'ModuleTypes', they're guaranteed to be present and translated.
--
-- See 'UCCrux.LLVM.FullType.MemType.asFullType' for where partiality is
-- avoided. Since this function is ubiquitous, this is a big win.
data TranslatedTypes arch = forall m.
  TranslatedTypes
  { translatedModuleTypes :: ModuleTypes m,
    translatedDeclTypes :: DeclTypes m arch
  }

data TypeTranslationError
  = -- | Couldn't find CFG in translated module
    NoCFG !L.Symbol
  | -- | Couldn't lift types in declaration to 'MemType'
    BadLift !String
  | -- | Wrong number of arguments after lifting declaration
    BadLiftArgs !L.Symbol
  | FullTypeTranslation L.Ident

ppTypeTranslationError :: TypeTranslationError -> String
ppTypeTranslationError =
  \case
    NoCFG (L.Symbol name) -> "Couldn't find definition of function " <> name
    BadLift name -> "Couldn't lift argument/return types to MemTypes for " <> name
    BadLiftArgs (L.Symbol name) ->
      "Wrong number of arguments after lifting declaration of " <> name
    FullTypeTranslation (L.Ident ident) ->
      "Couldn't find or couldn't translate type: " <> ident

-- | Debug intrinsics don't have their types translated because
--
-- * It's not necessary - overrides for these are installed as part of
--   crucible-llvm's default set for LLVM intrinsics.
-- * 'FullType' doesn\'t have a notion of metadatatype, and it\'s nice to keep
--   it that way to avoid a bunch of spurrious/impossible cases elsewhere.
isDebug :: L.Declare -> Bool
isDebug = ("llvm.dbg" `List.isPrefixOf`) . getNm . L.decName
  where
    getNm (L.Symbol nm) = nm

translateModuleDefines ::
  forall arch.
  ( ?lc :: TypeContext,
    ArchOk arch
  ) =>
  L.Module ->
  ModuleTranslation arch ->
  Either TypeTranslationError (TranslatedTypes arch)
translateModuleDefines llvmModule trans =
  case makeModuleTypes ?lc of
    Some initialModuleTypes ->
      let (maybeResult, modTypes) =
            runState
              ( runExceptT
                  ( (++)
                      <$> mapM translateDefine (L.modDefines llvmModule)
                      <*> mapM
                        translateDeclare
                        ( filter
                            (not . isDebug)
                            (L.modDeclares llvmModule)
                        )
                  )
              )
              initialModuleTypes
       in TranslatedTypes modTypes . DeclTypes . Map.fromList <$> maybeResult
  where
    translateDefine ::
      L.Define ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (L.Symbol, FunctionTypes m arch)
    translateDefine defn =
      do
        let decl = LLVMTrans.declareFromDefine defn
        liftedDecl <-
          case LLVMTrans.liftDeclare decl of
            Left err -> throwError (BadLift err)
            Right d -> pure d
        Crucible.AnyCFG cfg <-
          case Map.lookup (L.decName decl) (LLVMTrans.cfgMap trans) of
            Just (_, anyCfg) -> pure anyCfg
            Nothing -> throwError (NoCFG (L.decName decl))
        let crucibleTypes = Crucible.cfgArgTypes cfg
        let memTypes = fdArgTypes liftedDecl
        let isVarArgs = fdVarArgs liftedDecl
        -- Do the MemTypes agree with the Crucible types on the number of
        -- arguments? (Note that a variadic function has an "extra" argument
        -- after being translated to a CFG, hence the "+1")
        let matchedNumArgTypes =
              let numCrucibleTypes = Ctx.sizeInt (Ctx.size crucibleTypes)
               in length memTypes == numCrucibleTypes
                    || ( isVarArgs
                           && length memTypes + 1 == numCrucibleTypes
                       )

        unless matchedNumArgTypes (throwError (BadLiftArgs (L.decName decl)))
        Some fullTypes <-
          Ctx.generateSomeM
            ( Ctx.sizeInt (Ctx.size crucibleTypes)
                - if isVarArgs
                  then 1
                  else 0
            )
            ( \idx ->
                do
                  -- NOTE(lb): The indexing here is safe because of the "unless
                  -- matchedNumArgTypes" just above.
                  Some fullTypeRepr <-
                    withExceptT FullTypeTranslation $
                      toFullTypeM (memTypes !! idx)
                  pure $ Some fullTypeRepr
            )
        retType <-
          traverse
            (withExceptT FullTypeTranslation . toFullTypeM)
            (fdRetType liftedDecl)
        Some crucibleTypes' <-
          pure $
            if isVarArgs
              then removeVarArgsRepr crucibleTypes
              else Some crucibleTypes
        case testCompatibilityAssign (Proxy :: Proxy arch) fullTypes crucibleTypes' of
          Just Refl ->
            pure
              ( L.decName decl,
                FunctionTypes
                  { ftArgTypes = MatchingAssign fullTypes crucibleTypes',
                    ftRetType = retType,
                    ftIsVarArgs = boolToVarArgsRepr isVarArgs
                  }
              )
          Nothing ->
            panic
              "Impossible"
              ["(toCrucibleType . toFullTypeM) should be the identity function"]

    -- In this case, we don't have any Crucible types on hand to test
    -- compatibility with, they're just manufactured from the FullTypeReprs
    translateDeclare ::
      L.Declare ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (L.Symbol, FunctionTypes m arch)
    translateDeclare decl =
      do
        liftedDecl <-
          case LLVMTrans.liftDeclare decl of
            Left err -> throwError (BadLift err)
            Right d -> pure d
        let memTypes = fdArgTypes liftedDecl
        let isVarArgs = fdVarArgs liftedDecl
        Some fullTypes <-
          Ctx.generateSomeM
            (length memTypes)
            ( \idx ->
                do
                  Some fullTypeRepr <-
                    withExceptT FullTypeTranslation $
                      toFullTypeM (memTypes !! idx)
                  pure $ Some fullTypeRepr
            )
        retType <-
          traverse
            (withExceptT FullTypeTranslation . toFullTypeM)
            (fdRetType liftedDecl)
        SomeAssign' crucibleTypes Refl _ <-
          pure $ assignmentToCrucibleType (Proxy :: Proxy arch) fullTypes
        pure
          ( L.decName decl,
            FunctionTypes
              { ftArgTypes = MatchingAssign fullTypes crucibleTypes,
                ftRetType = retType,
                ftIsVarArgs = boolToVarArgsRepr isVarArgs
              }
          )

    removeVarArgsRepr ::
      Ctx.Assignment CrucibleTypes.TypeRepr ctx ->
      Some (Ctx.Assignment CrucibleTypes.TypeRepr)
    removeVarArgsRepr crucibleTypes =
      case Ctx.viewAssign crucibleTypes of
        Ctx.AssignEmpty ->
          panic
            "translateModuleDefines"
            ["varargs function with no arguments"]
        Ctx.AssignExtend rest vaRepr ->
          case testEquality vaRepr LLVMTrans.varArgsRepr of
            Just Refl -> Some rest
            Nothing ->
              panic
                "translateModuleDefines"
                ["varargs function with no varargs repr"]

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
