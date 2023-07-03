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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Overrides.Skip
  ( SkipOverrideName (..),
    unsoundSkipOverrides,
    createSkipOverride,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), use, to)
import           Control.Monad.IO.Class (liftIO)
import           Data.IORef (IORef, modifyIORef)
import           Data.Maybe (fromMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))

import qualified Text.LLVM.AST as L

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))

-- what4
import           What4.FunctionName (functionName)

-- crucible
import           Lang.Crucible.Backend (IsSymBackend)
import           Lang.Crucible.FunctionHandle (SomeHandle(..), handleMapToHandles, handleName)
import           Lang.Crucible.Simulator.ExecutionTree (functionBindings, stateContext, fnBindings)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override
import qualified Lang.Crucible.Types as CTy

-- crucible-llvm
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, MemImpl, MemOptions)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation, transContext, llvmTypeCtx)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (LLVMOverride(..), basic_llvm_override)

import           Crux.Types (OverM)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Context.Module (ModuleContext, funcTypes, moduleDecls)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.CrucibleType (SomeAssign'(..),  assignmentToCrucibleType, toCrucibleReturnType)
import           UCCrux.LLVM.ExprTracker (ExprTracker)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr(FuncSigRepr))
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.Type (MapToCrucibleType)
import qualified UCCrux.LLVM.FullType.VarArgs as VA
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbol, makeFuncSymbol, isDebug, funcSymbolToString)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride)
import           UCCrux.LLVM.Postcondition.Apply (applyPostcond)
import qualified UCCrux.LLVM.Postcondition.Type as Post
import           UCCrux.LLVM.Postcondition.Type (UPostcond)
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
-- This won't register overrides for functions that already have associated
-- CFGs, like if you already registered a normal override for `free` or similar.
unsoundSkipOverrides ::
  ( IsSymBackend sym bak,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  ModuleContext m arch ->
  bak ->
  ModuleTranslation arch ->
  -- | Set of skip overrides encountered during execution, see Note [IORefs].
  IORef (Set SkipOverrideName) ->
  -- | Origins of created values. See Note [IORefs].
  IORef (ExprTracker m sym argTypes) ->
  -- | Postconditions of each override (constraints on return values,
  -- information about clobbered pointer values such as arguments or global
  -- variables)
  Map (FuncSymbol m) (UPostcond m) ->
  [L.Declare] ->
  OverM personality sym LLVM [PolymorphicLLVMOverride arch (personality sym) sym]
unsoundSkipOverrides modCtx bak mtrans usedRef annotationRef postconds decls =
  do
    let llvmCtx = mtrans ^. transContext
    let ?lc = llvmCtx ^. llvmTypeCtx
    binds <- use (stateContext . functionBindings)
    let alreadyDefined =
          Set.fromList $
            map
              (\(SomeHandle hand) -> functionName (handleName hand))
              (handleMapToHandles (fnBindings binds))
    let create decl =
          case modCtx ^. funcTypes . to (makeFuncSymbol (L.decName decl)) of
            Nothing ->
              panic
                "unsoundSkipOverrides"
                ["Precondition violation: Declaration not in module"]
            Just funcSym ->
              let post =
                    case modCtx ^. funcTypes . funcSymbol funcSym of
                      Some (FuncSigRepr _ _ ret) ->
                        fromMaybe
                          (Post.minimalUPostcond ret)
                          (Map.lookup funcSym postconds)
              in createSkipOverride modCtx bak usedRef annotationRef post funcSym

    pure $
      map
        create
        ( filter
            ((`Set.notMember` alreadyDefined) . declName)
            (filter (not . isDebug) decls)
        )

-- | Boilerplate to create an LLVM override
mkOverride ::
  ( IsSymBackend sym bak,
    HasLLVMAnn sym,
    ArchOk arch
  ) =>
  ModuleContext m arch ->
  proxy bak ->
  -- | Function to be overridden
  FuncSymbol m ->
  -- | Implementation
  (forall fs va mft args.
    (fs ~ 'FS.FuncSig va mft args) =>
    FuncSigRepr m fs ->
    MemImpl sym ->
    Ctx.Assignment (Crucible.RegEntry sym) (MapToCrucibleType arch args) ->
    IO (Crucible.RegValue sym (FS.ReturnTypeToCrucibleType arch mft), MemImpl sym)) ->
  PolymorphicLLVMOverride arch (personality sym) sym
mkOverride modCtx _proxy funcSymb impl =
  -- There's a lot of duplication here because the case over whether or not the
  -- function is varargs can't be pushed further down; doing so causes "type is
  -- untouchable inside..." errors
  case modCtx ^. funcTypes . funcSymbol funcSymb of
    Some fs@(FuncSigRepr VA.IsVarArgsRepr argFTys retTy) ->
      case assignmentToCrucibleType modCtx argFTys of
        SomeAssign' argTys Refl _ ->
          makePolymorphicLLVMOverride $
            basic_llvm_override $
              LLVMOverride
                { llvmOverride_declare = decl,
                  llvmOverride_args = argTys Ctx.:> CTy.VectorRepr CTy.AnyRepr,
                  llvmOverride_ret = toCrucibleReturnType modCtx retTy,
                  llvmOverride_def =
                    \mvar _sym (args Ctx.:> _) ->
                      Override.modifyGlobal mvar (\mem -> liftIO (impl fs mem args))
                }
    Some fs@(FuncSigRepr VA.NotVarArgsRepr argFTys retTy) ->
      case assignmentToCrucibleType modCtx argFTys of
        SomeAssign' argTys Refl _ ->
          makePolymorphicLLVMOverride $
            basic_llvm_override $
              LLVMOverride
                { llvmOverride_declare = decl,
                  llvmOverride_args = argTys,
                  llvmOverride_ret = toCrucibleReturnType modCtx retTy,
                  llvmOverride_def =
                    \mvar _sym args ->
                      Override.modifyGlobal mvar (\mem -> liftIO (impl fs mem args))
                }
  where decl = modCtx ^. moduleDecls . funcSymbol funcSymb


-- | Create an override that takes the place of a given defined or even
-- declared/external function, and instead of executing that function,
-- instead manufactures a fresh symbolic return value and optionally clobbers
-- some parts of its arguments or global variables with fresh symbolic values.
--
-- Useful for continuing symbolic execution in the presence of external/library
-- functions.
createSkipOverride ::
  forall m arch sym bak argTypes personality.
  ( IsSymBackend sym bak,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  ModuleContext m arch ->
  bak ->
  -- | Set of skip overrides encountered during execution, see Note [IORefs].
  IORef (Set SkipOverrideName) ->
  -- | Origins of created values. See Note [IORefs].
  IORef (ExprTracker m sym argTypes) ->
  -- | Constraints on the return value, clobbered pointer values such as
  -- arguments or global variables
  UPostcond m ->
  -- | Function to be overridden
  FuncSymbol m ->
  PolymorphicLLVMOverride arch (personality sym) sym
createSkipOverride modCtx bak usedRef annotationRef postcond funcSymb =
  mkOverride modCtx (Just bak) funcSymb $
    \fs mem args ->
      do let name = modCtx ^. moduleDecls . funcSymbol funcSymb . to declName
         modifyIORef usedRef (Set.insert (SkipOverrideName name))
         case Post.typecheckPostcond postcond fs of
           Left err ->
             panic
               "createSkipOverride"
               [ "Ill-typed postcondition for " ++ funcSymbolToString funcSymb
               , "Error:"
               , show (Post.ppPostcondTypeError err)
               , "Function signature:"
               , show (FS.ppFuncSigRepr fs)
               , "Postcondition:"
               , show (Post.ppUPostcond postcond)
               ]
           Right pc ->
             let ret = FS.fsRetType fs
             in applyPostcond bak modCtx annotationRef funcSymb pc ret mem args
