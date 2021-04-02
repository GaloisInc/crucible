{-
Module           : UCCrux.LLVM.FullType.Translation
Description      : Translation
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.Translation
  ( FunctionTypes (..),
    MatchingAssign (..),
    DeclTypes,
    GlobalSymbol,
    GlobalMap,
    TranslatedTypes (..),
    TypeTranslationError (..),
    isDebug,
    translateModuleDefines,
    ppTypeTranslationError,
    lookupDeclTypes,
    lookupGlobalSymbol,
    makeGlobalSymbol,
    getGlobalSymbol,
    isEmptyGlobalMap,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (unzip)

import           Control.Lens.At (At(at), Ixed(ix), Index, IxValue, ixAt)
import           Control.Lens (lens)
import           Control.Monad (unless)
import           Control.Monad.Except (ExceptT, runExceptT, throwError, withExceptT)
import           Control.Monad.State (State, runState)
import           Data.Functor ((<&>))
import qualified Data.List as List
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           Lang.Crucible.LLVM.MemType (fdArgTypes, fdRetType, fdVarArgs)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Crux.LLVM.Overrides (ArchOk)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.CrucibleType (SomeAssign'(..), testCompatibilityAssign, assignmentToCrucibleType)
import           UCCrux.LLVM.FullType.Type
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr, boolToVarArgsRepr)
{- ORMOLU_ENABLE -}

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

newtype GlobalSymbol m = GlobalSymbol
  {_getGlobalSymbol :: L.Symbol}
  deriving (Eq, Ord)

type instance Index (GlobalMap m a) = GlobalSymbol m
type instance IxValue (GlobalMap m a) = a

-- | Constructor not exported to enforce the invariant that a 'GlobalMap' holds
-- a value for every LLVM global in the corresponding module indicated by the
-- @m@ parameter.
newtype GlobalMap m a = GlobalMap
  {getGlobalMap :: Map (GlobalSymbol m) a}
  deriving (Foldable, Functor)

instance At (GlobalMap m a) where
  at symb = lens getGlobalMap (const GlobalMap) . at symb

instance Ixed (GlobalMap m a) where
  ix = ixAt

lookupGlobalSymbol :: GlobalSymbol m -> GlobalMap m a -> a
lookupGlobalSymbol symbol (GlobalMap mp) =
  fromMaybe
    ( panic
        "lookupGlobalSymbol"
        ["Broken invariant: GlobalSymbol not present in GlobalMap"]
    )
    (Map.lookup symbol mp)

makeGlobalSymbol :: GlobalMap m a -> L.Symbol -> Maybe (GlobalSymbol m)
makeGlobalSymbol (GlobalMap mp) symbol =
  let gs = GlobalSymbol symbol
   in case Map.lookup gs mp of
        Just _ -> Just gs
        Nothing -> Nothing

getGlobalSymbol :: GlobalSymbol m -> L.Symbol
getGlobalSymbol (GlobalSymbol s) = s

isEmptyGlobalMap :: GlobalMap m a -> Bool
isEmptyGlobalMap (GlobalMap m) = Map.null m

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
    translatedGlobalTypes :: GlobalMap m (Some (FullTypeRepr m)),
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
              ( runExceptT $
                  (,)
                    <$> ( (++)
                            <$> mapM translateDefine (L.modDefines llvmModule)
                            <*> mapM
                              translateDeclare
                              ( filter
                                  (not . isDebug)
                                  (L.modDeclares llvmModule)
                              )
                        )
                    <*> mapM translateGlobal (L.modGlobals llvmModule)
              )
              initialModuleTypes
       in maybeResult
            <&> \(declTypes, globalTypes) ->
              TranslatedTypes
                modTypes
                (GlobalMap (Map.fromList globalTypes))
                (DeclTypes (Map.fromList declTypes))
  where
    translateGlobal ::
      L.Global ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (GlobalSymbol m, Some (FullTypeRepr m))
    translateGlobal glob =
      do
        memTy <- withExceptT BadLift (LLVMTrans.liftMemType (L.globalType glob))
        ty <- withExceptT FullTypeTranslation (toFullTypeM memTy)
        pure (GlobalSymbol (L.globalSym glob), ty)

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
