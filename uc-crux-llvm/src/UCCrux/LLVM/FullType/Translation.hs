{-
Module           : UCCrux.LLVM.FullType.Translation
Description      : Translation
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.Translation
  ( FunctionTypes (..),
    MatchingAssign (..),
    TranslatedTypes (..),
    TypeTranslationError,
    translateModuleDefines,
    ppTypeTranslationError,
    throwTypeTranslationError,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (unzip)

import           Control.Monad (unless)
import           Control.Monad.Except (ExceptT, runExceptT, throwError, withExceptT)
import           Control.Monad.State (State, runState)
import           Data.Functor ((<&>))
import           Data.Proxy (Proxy(Proxy))
import qualified Data.Map as Map

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

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
import           UCCrux.LLVM.Errors.MalformedLLVMModule (malformedLLVMModule)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.CrucibleType (SomeAssign'(..), testCompatibilityAssign, assignmentToCrucibleType)
import           UCCrux.LLVM.FullType.Type
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr, boolToVarArgsRepr)
import           UCCrux.LLVM.Module (Module, FuncMap(..), GlobalMap, moduleDeclMap, moduleDefnMap, moduleGlobalMap)
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

-- | The existential quantification over @m@ here makes the @FullType@ API safe.
-- You can only intermingle 'FullTypeRepr' from the same LLVM module, and by
-- construction, the 'ModuleTypes' contains a 'FullTypeRepr' for every type
-- that\'s (transitively) mentioned in any of the types in the 'DeclTypes'.
-- Thus, you can avoid partiality when looking up type aliases in the
-- 'ModuleTypes', they're guaranteed to be present and translated.
--
-- See 'UCCrux.LLVM.FullType.MemType.asFullType' for where partiality is
-- avoided. Since this function is ubiquitous, this is a big win.
data TranslatedTypes arch =
  forall m.
  TranslatedTypes
  { translatedModule :: Module m,
    translatedModuleTypes :: ModuleTypes m,
    translatedGlobalTypes :: GlobalMap m (Some (FullTypeRepr m)),
    translatedFuncTypes :: FuncMap m (FunctionTypes m arch)
  }

data TypeTranslationError
  = -- | Couldn't find CFG in translated module
    NoCFG !L.Symbol
  | -- | Couldn't lift types in declaration to 'MemType'
    BadLift !String
  | -- | Wrong number of arguments after lifting declaration
    BadLiftArgs !L.Symbol
  | FullTypeTranslation L.Ident

ppTypeTranslationError :: TypeTranslationError -> Doc ann
ppTypeTranslationError =
  PP.pretty .
    \case
      NoCFG (L.Symbol name) -> "Couldn't find definition of function " <> name
      BadLift name -> "Couldn't lift argument/return types to MemTypes for " <> name
      BadLiftArgs (L.Symbol name) ->
        "Wrong number of arguments after lifting declaration of " <> name
      FullTypeTranslation (L.Ident ident) ->
        "Couldn't find or couldn't translate type: " <> ident

throwTypeTranslationError :: TypeTranslationError -> a
throwTypeTranslationError err =
  case err of
    NoCFG {} -> doPanic
    BadLift {} -> isMalformed
    BadLiftArgs {} -> doPanic
    FullTypeTranslation {} -> doPanic
  where
    nm = "throwTypeTranslationError"
    doPanic = panic nm [show (ppTypeTranslationError err)]
    isMalformed = malformedLLVMModule nm (ppTypeTranslationError err) []


-- | Precondition: The 'TypeContext' must correspond to the 'L.Module'.
translateModuleDefines ::
  forall arch.
  ( ?lc :: TypeContext,
    ArchOk arch
  ) =>
  L.Module ->
  ModuleTranslation arch ->
  Either TypeTranslationError (TranslatedTypes arch)
translateModuleDefines llvmModule trans =
  case makeModuleTypes llvmModule ?lc of
    ModuleAndTypes m initialModuleTypes ->
      let (maybeResult, modTypes) =
            runState
              ( runExceptT $
                  (,,)
                    <$> traverse translateDeclare (moduleDeclMap m)
                    <*> traverse translateDefine (moduleDefnMap m)
                    <*> traverse translateGlobal (moduleGlobalMap m)
              )
              initialModuleTypes
       in maybeResult
            <&> \(declTypes, defnTypes, globalTypes) ->
              TranslatedTypes
                { translatedModule = m,
                  translatedModuleTypes = modTypes,
                  translatedGlobalTypes = globalTypes,
                  translatedFuncTypes = FuncMap declTypes defnTypes
                }
  where
    translateGlobal ::
      L.Global ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (Some (FullTypeRepr m))
    translateGlobal glob =
      do
        memTy <- withExceptT BadLift (LLVMTrans.liftMemType (L.globalType glob))
        withExceptT FullTypeTranslation (toFullTypeM memTy)

    translateDefine ::
      L.Define ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (FunctionTypes m arch)
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
        case testCompatibilityAssign (Proxy @arch) fullTypes crucibleTypes' of
          Just Refl ->
            pure $
              FunctionTypes
                { ftArgTypes = MatchingAssign fullTypes crucibleTypes',
                  ftRetType = retType,
                  ftIsVarArgs = boolToVarArgsRepr isVarArgs
                }
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
        (FunctionTypes m arch)
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
          pure $ assignmentToCrucibleType (Proxy @arch) fullTypes
        pure $
          FunctionTypes
            { ftArgTypes = MatchingAssign fullTypes crucibleTypes,
              ftRetType = retType,
              ftIsVarArgs = boolToVarArgsRepr isVarArgs
            }

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
