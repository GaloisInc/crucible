{-
Module       : UCCrux.LLVM.Overrides.Skip
Description  : Unsound overrides for skipping execution of functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.Overrides.Skip
  ( SkipOverrideName (..),
    unsoundSkipOverrides,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), use)
import           Control.Monad.IO.Class (liftIO)
import           Data.IORef (IORef, modifyIORef)
import           Data.Maybe (mapMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

-- what4
import           What4.FunctionName (functionName)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.FunctionHandle (SomeHandle(..), handleMapToHandles, handleName)
import           Lang.Crucible.Simulator.ExecutionTree (functionBindings, stateContext, fnBindings)
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation, transContext, llvmTypeCtx, llvmDeclToFunHandleRepr')
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate(..), LLVMOverride(..), basic_llvm_override)

import           Crux.Types (OverM, Model, HasModel)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
{- ORMOLU_ENABLE -}

newtype SkipOverrideName = SkipOverrideName {getSkipOverrideName :: Text}
  deriving (Eq, Ord, Show)

declName :: L.Declare -> Text
declName decl =
  let L.Symbol name = L.decName decl
   in Text.pack name

-- | Additional overrides that are useful for bugfinding, but not for
-- verification. They skip execution of the specified functions.
--
-- Mostly useful for functions that are declared but not defined.
--
-- Note that this won't register overrides for functions that already have
-- associated CFGs, like if you already registered a normal override for `free`
-- or similar.
unsoundSkipOverrides ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    HasModel personality
  ) =>
  proxy arch ->
  ModuleTranslation arch ->
  IORef (Set SkipOverrideName) ->
  [L.Declare] ->
  OverM Model sym LLVM [OverrideTemplate (personality sym) sym arch rtp l a]
unsoundSkipOverrides proxy mtrans usedRef decls =
  do
    let llvmCtx = mtrans ^. transContext
    let ?lc = llvmCtx ^. llvmTypeCtx
    binds <- use (stateContext . functionBindings)
    let alreadyDefined =
          Set.fromList $
            map
              (\(SomeHandle hand) -> functionName (handleName hand))
              (handleMapToHandles (fnBindings binds))
    pure $
      mapMaybe
        (createSkipOverride proxy usedRef)
        (filter ((`Set.notMember` alreadyDefined) . declName) decls)

-- TODO(lb): Currently only works for void functions, should be extended to
-- handle non-void functions.
createSkipOverride ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    HasModel personality
  ) =>
  proxy arch ->
  IORef (Set SkipOverrideName) ->
  L.Declare ->
  Maybe (OverrideTemplate (personality sym) sym arch rtp l a)
createSkipOverride _proxy usedRef decl =
  llvmDeclToFunHandleRepr' decl $ \args ret ->
    Just $
      basic_llvm_override $
        LLVMOverride
          { llvmOverride_declare = decl,
            llvmOverride_args = args,
            llvmOverride_ret = ret,
            llvmOverride_def =
              \_memOps _sym _args ->
                do
                  let name = declName decl
                  liftIO $
                    modifyIORef usedRef (Set.insert (SkipOverrideName name))
                  case ret of
                    CrucibleTypes.UnitRepr -> pure ()
                    _ ->
                      unimplemented
                        "createSkipOverride"
                        (Unimplemented.NonVoidUndefinedFunc name)
          }
