{-
Module       : UCCrux.LLVM.Context.Function
Description  : LLVM function-level read-only context.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Context.Function
  ( FunctionContext (..),
    FunctionContextError (..),
    ppFunctionContextError,
    makeFunctionContext,
    functionName,
    argumentNames,
    argumentCrucibleTypes,
    argumentFullTypes,
    argumentMemTypes,
    argumentStorageTypes,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Monad (when)
import           Control.Lens ((^.), Simple, Lens, lens)
import           Data.Functor.Const (Const(Const, getConst))
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Monoid (getFirst, First(First))
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (forFC, fmapFC, TraversableFC(traverseFC))

import qualified Lang.Crucible.Types as CrucibleTypes
import           Lang.Crucible.LLVM.MemModel (toStorableType, StorageType, withPtrWidth)
import           Lang.Crucible.LLVM.MemType (fdArgTypes, MemType)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans

import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.Module (ModuleContext, withTypeContext, llvmModule, moduleTranslation)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(VarArgsFunction))
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr, MapToCrucibleType)
import           UCCrux.LLVM.Module (DefnSymbol, defnSymbol, getDefnSymbol, moduleDefnMap, getModule)
{- ORMOLU_ENABLE -}

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data FunctionContext m arch (argTypes :: Ctx (FullType m)) = FunctionContext
  { _functionName :: Text,
    _argumentFullTypes :: Ctx.Assignment (FullTypeRepr m) argTypes,
    _argumentCrucibleTypes :: CrucibleTypes.CtxRepr (MapToCrucibleType arch argTypes),
    _argumentMemTypes :: Ctx.Assignment (Const MemType) argTypes,
    _argumentStorageTypes :: Ctx.Assignment (Const StorageType) argTypes,
    _argumentNames :: Ctx.Assignment (Const (Maybe Text)) argTypes
  }

functionName :: Simple Lens (FunctionContext m arch argTypes) Text
functionName = lens _functionName (\s v -> s {_functionName = v})

argumentNames :: Simple Lens (FunctionContext m arch argTypes) (Ctx.Assignment (Const (Maybe Text)) argTypes)
argumentNames = lens _argumentNames (\s v -> s {_argumentNames = v})

argumentCrucibleTypes :: Simple Lens (FunctionContext m arch argTypes) (CrucibleTypes.CtxRepr (MapToCrucibleType arch argTypes))
argumentCrucibleTypes = lens _argumentCrucibleTypes (\s v -> s {_argumentCrucibleTypes = v})

argumentFullTypes :: Simple Lens (FunctionContext m arch argTypes) (Ctx.Assignment (FullTypeRepr m) argTypes)
argumentFullTypes = lens _argumentFullTypes (\s v -> s {_argumentFullTypes = v})

argumentMemTypes :: Simple Lens (FunctionContext m arch argTypes) (Ctx.Assignment (Const MemType) argTypes)
argumentMemTypes = lens _argumentMemTypes (\s v -> s {_argumentMemTypes = v})

argumentStorageTypes :: Simple Lens (FunctionContext m arch argTypes) (Ctx.Assignment (Const StorageType) argTypes)
argumentStorageTypes = lens _argumentStorageTypes (\s v -> s {_argumentStorageTypes = v})

data FunctionContextError
  = -- | Couldn't find 'L.Define' of entrypoint
    MissingEntrypoint Text
  | -- | Couldn't lift types in declaration to 'MemType'
    BadLift Text
  | -- | Wrong number of arguments after lifting declaration
    BadLiftArgs !Int !Int !Int
  | -- | Couldn't lift a 'MemType' to a 'StorageType'
    BadMemType MemType

ppFunctionContextError :: FunctionContextError -> Text
ppFunctionContextError =
  \case
    MissingEntrypoint name -> "Couldn't find definition of function " <> name
    BadLift name -> "Couldn't lift argument/return types to MemTypes for " <> name
    BadLiftArgs decl tys idx ->
      Text.unwords
        [ "Wrong number of arguments after lifting declaration.",
          "In the declaration there were "
            <> Text.pack
              (show decl)
            <> " MemTypes.",
          "Attempted to map these to " <> Text.pack (show tys)
            <> " other types.",
          "Couldn't find one at index "
            <> Text.pack (show idx)
            <> "."
        ]
    BadMemType _ -> "Bad MemType"

withPtrWidthOf ::
  LLVMTrans.ModuleTranslation arch ->
  (ArchOk arch => b) ->
  b
withPtrWidthOf trans k =
  LLVMTrans.llvmPtrWidth (trans ^. LLVMTrans.transContext) (\ptrW -> withPtrWidth ptrW k)

-- | This function does some precomputation of ubiquitously used values, and
-- some handling of what should generally be very rare errors.
makeFunctionContext ::
  forall m arch fullTypes.
  ArchOk arch =>
  ModuleContext m arch ->
  DefnSymbol m ->
  Ctx.Assignment (FullTypeRepr m) fullTypes ->
  Ctx.Assignment CrucibleTypes.TypeRepr (MapToCrucibleType arch fullTypes) ->
  Either FunctionContextError (FunctionContext m arch fullTypes)
makeFunctionContext modCtx defnSymb argFullTypes argTypes =
  do
    let llvmMod = modCtx ^. llvmModule
    let L.Symbol strName = getDefnSymbol defnSymb
    let name = Text.pack strName
    let def = moduleDefnMap llvmMod ^. defnSymbol defnSymb
    when (L.defVarArgs def) $
      unimplemented "makeFunctionContext" VarArgsFunction
    let trans = modCtx ^. moduleTranslation
    funDecl <-
      withTypeContext modCtx $
        case LLVMTrans.liftDeclare (LLVMTrans.declareFromDefine def) of
          Left err -> Left (BadLift (Text.pack err))
          Right d -> Right d
    argMemTypes <-
      case maybeMapToContext
        (Ctx.size argFullTypes)
        (Map.fromList (zip [0 ..] (fdArgTypes funDecl))) of
        Right types -> Right types
        Left idx -> Left (BadLiftArgs (length (fdArgTypes funDecl)) (Ctx.sizeInt (Ctx.size argFullTypes)) idx)
    argStorageTypes <-
      withPtrWidthOf trans $
        forFC
          argMemTypes
          ( \(Const memType) ->
              case toStorableType memType of
                Just storeTy -> Right (Const storeTy)
                Nothing -> Left (BadMemType memType)
          )
    pure $
      FunctionContext
        { _functionName = name,
          _argumentFullTypes = argFullTypes,
          _argumentCrucibleTypes = argTypes,
          _argumentMemTypes = argMemTypes,
          _argumentStorageTypes = argStorageTypes,
          _argumentNames =
            fmapFC
              (Const . getFirst . getConst)
              ( mapToContext
                  (Ctx.size argFullTypes)
                  (fmap (First . Just) (debugInfoArgNames (getModule llvmMod) def))
              )
        }

mapToContext ::
  Monoid a =>
  Ctx.Size items ->
  Map Int a ->
  Ctx.Assignment (Const a) items
mapToContext size mp =
  Ctx.generate
    size
    (\index -> Const (Map.findWithDefault mempty (Ctx.indexVal index) mp))

maybeMapToContext ::
  Ctx.Size items ->
  Map Int a ->
  Either Int (Ctx.Assignment (Const a) items)
maybeMapToContext size mp =
  traverseFC (fmap Const . getConst) $
    Ctx.generate
      size
      ( \index ->
          Const
            ( case Map.lookup (Ctx.indexVal index) mp of
                Just val -> Right val
                Nothing -> Left (Ctx.indexVal index)
            )
      )

-- Stolen shamelessly from saw-script
debugInfoArgNames :: L.Module -> L.Define -> Map Int Text
debugInfoArgNames m d =
  case Map.lookup "dbg" $ L.defMetadata d of
    Just (L.ValMdRef s) -> scopeArgs s
    _ -> Map.empty
  where
    scopeArgs :: Int -> Map Int Text
    scopeArgs s = go $ L.modUnnamedMd m
      where
        go :: [L.UnnamedMd] -> Map Int Text
        go [] = Map.empty
        go
          ( L.UnnamedMd
              { L.umValues =
                  L.ValMdDebugInfo
                    ( L.DebugInfoLocalVariable
                        L.DILocalVariable
                          { L.dilvScope = Just (L.ValMdRef s'),
                            L.dilvArg = a,
                            L.dilvName = Just n
                          }
                      )
              }
              : xs
            ) =
            if s == s' then Map.insert (fromIntegral a - 1) (Text.pack n) $ go xs else go xs
        go (_ : xs) = go xs
