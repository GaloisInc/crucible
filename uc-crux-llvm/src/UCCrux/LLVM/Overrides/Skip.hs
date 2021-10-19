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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Overrides.Skip
  ( SkipOverrideName (..),
    unsoundSkipOverrides,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), use, to)
import           Control.Monad.IO.Class (liftIO)
import           Data.IORef (IORef, modifyIORef)
import           Data.Maybe (mapMaybe)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl), testEquality)

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Some (Some(Some))

-- what4
import qualified What4.Interface as What4
import           What4.FunctionName (functionName)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.FunctionHandle (SomeHandle(..), handleMapToHandles, handleName)
import           Lang.Crucible.Simulator.ExecutionTree (functionBindings, stateContext, fnBindings)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, MemImpl)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation, transContext, llvmTypeCtx, llvmDeclToFunHandleRepr')
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (LLVMOverride(..), basic_llvm_override)

import           Crux.Types (OverM)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (ConstrainedTypedValue(..), minimalConstrainedShape)
import           UCCrux.LLVM.Context.Module (ModuleContext, funcTypes)
import           UCCrux.LLVM.Cursor (Selector(SelectReturn), Cursor(Here))
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import           UCCrux.LLVM.FullType.Translation (FunctionTypes, ftRetType)
import           UCCrux.LLVM.Module (FuncSymbol, funcSymbol, makeFuncSymbol, isDebug)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, makePolymorphicLLVMOverride)
import           UCCrux.LLVM.Setup (SymValue(getSymValue), generate)
import           UCCrux.LLVM.Setup.Assume (assume)
import           UCCrux.LLVM.Setup.Monad (TypedSelector, runSetup, resultAssumptions, resultMem, resultAnnotations)
import qualified UCCrux.LLVM.Shape as Shape
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
    ?lc :: TypeContext
  ) =>
  ModuleContext m arch ->
  sym ->
  ModuleTranslation arch ->
  -- | Set of skip overrides encountered during execution
  IORef (Set SkipOverrideName) ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | Postconditions of each override (constraints on return values)
  Map (FuncSymbol m) (ConstrainedTypedValue m) ->
  [L.Declare] ->
  OverM personality sym LLVM [PolymorphicLLVMOverride (personality sym) sym arch]
unsoundSkipOverrides modCtx sym mtrans usedRef annotationRef postconditions decls =
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
              createSkipOverride
                modCtx
                sym
                usedRef
                annotationRef
                (Map.lookup funcSym postconditions)
                decl
                funcSym
    pure $
      mapMaybe
        create
        ( filter
            ((`Set.notMember` alreadyDefined) . declName)
            (filter (not . isDebug) decls)
        )

-- TODO(lb): At some point, it'd be nice to apply heuristics to the manufactured
-- return values, similar to those for function arguments. To do this, this
-- function would probably need to take an IORef in which to insert annotations
-- for values it creates.
createSkipOverride ::
  forall m arch sym argTypes personality.
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext
  ) =>
  ModuleContext m arch ->
  sym ->
  IORef (Set SkipOverrideName) ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  Maybe (ConstrainedTypedValue m) ->
  L.Declare ->
  FuncSymbol m ->
  Maybe (PolymorphicLLVMOverride (personality sym) sym arch)
createSkipOverride modCtx sym usedRef annotationRef postcondition decl funcSym =
  llvmDeclToFunHandleRepr' decl $
    \args ret ->
      Just $
        makePolymorphicLLVMOverride $
          basic_llvm_override $
            LLVMOverride
              { llvmOverride_declare = decl,
                llvmOverride_args = args,
                llvmOverride_ret = ret,
                llvmOverride_def =
                  \mvar _sym _args ->
                    do
                      liftIO $
                        modifyIORef usedRef (Set.insert (SkipOverrideName name))
                      Override.modifyGlobal mvar $ \mem ->
                        liftIO
                          ( returnValue
                              mem
                              ret
                              (modCtx ^. funcTypes . funcSymbol funcSym)
                          )
              }
  where
    name = declName decl
    symbolName = L.decName decl

    returnValue ::
      MemImpl sym ->
      CrucibleTypes.TypeRepr ty ->
      FunctionTypes m arch ->
      IO (Crucible.RegValue sym ty, MemImpl sym)
    returnValue mem ret fTypes =
      case (ret, ftRetType fTypes) of
        (CrucibleTypes.UnitRepr, Nothing) -> pure ((), mem)
        (CrucibleTypes.UnitRepr, _) ->
          panic
            "createSkipOverride"
            ["Mismatched return types - CFG was void"]
        (_, Nothing) ->
          panic
            "createSkipOverride"
            ["Mismatched return types - CFG was non-void"]
        (_, Just (Some retFullType)) ->
          case testEquality (toCrucibleType (Proxy :: Proxy arch) retFullType) ret of
            Nothing ->
              panic
                "createSkipOverride"
                ["Mismatched return types"]
            Just Refl ->
              runSetup
                modCtx
                mem
                ( generate
                    sym
                    modCtx
                    retFullType
                    ( SelectReturn
                        ( case modCtx ^. funcTypes . to (makeFuncSymbol symbolName) of
                            Nothing ->
                              panic
                                "createSkipOverride"
                                [ "Precondition violation:",
                                  "Declaration not found in module:",
                                  show symbolName
                                ]
                            Just s -> s
                        )
                        (Here retFullType)
                    )
                    ( case postcondition of
                        Just (ConstrainedTypedValue ft shape) ->
                          case testEquality ft retFullType of
                            Just Refl -> shape
                            Nothing ->
                              panic
                                "createSkipOverride"
                                [ "Ill-typed constraints on return value for override "
                                    <> Text.unpack name
                                ]
                        Nothing -> minimalConstrainedShape retFullType
                    )
                )
                >>= \case
                  (result, value) ->
                    do
                      assume name sym (resultAssumptions result)
                      -- The keys are nonces, so they'll never clash, so the
                      -- bias of the union is unimportant.
                      modifyIORef annotationRef (Map.union (resultAnnotations result))
                      pure (value ^. Shape.tag . to getSymValue, resultMem result)
