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
  ( FuncSigRepr (..),
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
import qualified Data.Map as Map
import           GHC.Stack (HasCallStack)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as Crucible

import           Lang.Crucible.LLVM.MemType (fdArgTypes, fdRetType, fdVarArgs)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Crux.LLVM.Overrides (ArchOk)
import           UCCrux.LLVM.Errors.MalformedLLVMModule (malformedLLVMModule)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.FuncSig
import           UCCrux.LLVM.FullType.Type
import           UCCrux.LLVM.FullType.VarArgs (boolToVarArgsRepr)
import           UCCrux.LLVM.Module (Module, FuncMap(..), GlobalMap, moduleDeclMap, moduleDefnMap, moduleGlobalMap)
{- ORMOLU_ENABLE -}

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
    translatedFuncTypes :: FuncMap m (Some (FuncSigRepr m))
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

-- | Callers should also be annotated with 'HasCallStack'
throwTypeTranslationError :: HasCallStack => TypeTranslationError -> a
throwTypeTranslationError err =
  case err of
    NoCFG {} -> panic nm [show prettyErr]
    BadLift {} -> malformedLLVMModule prettyErr []
    BadLiftArgs {} -> panic nm [show prettyErr]
    FullTypeTranslation {} -> panic nm [show prettyErr]
  where
    prettyErr = ppTypeTranslationError err
    nm = "throwTypeTranslationError"


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
      ExceptT TypeTranslationError (State (ModuleTypes m)) (Some (FuncSigRepr m))
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
        translateDeclare decl

    -- In this case, we don't have any Crucible types on hand to test
    -- compatibility with, they're just manufactured from the FullTypeReprs
    translateDeclare ::
      L.Declare ->
      ExceptT TypeTranslationError (State (ModuleTypes m)) (Some (FuncSigRepr m))
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
        Some retTypeRepr <- return (mkReturnTypeRepr retType)
        Some vaRep <- return (boolToVarArgsRepr isVarArgs)
        pure (Some (FuncSigRepr vaRep fullTypes retTypeRepr))
