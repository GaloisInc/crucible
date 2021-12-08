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
    ClobberSpecs,
    makeClobberSpecs,
    ClobberSpec (..),
    ClobberSpecError (..),
    ppClobberSpecError,
    ClobberSelector (..),
    emptyClobberSpecs,
    SomeClobberSpec (..),
    unsoundSkipOverrides,
    createSkipOverride,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), use, to)
import           Control.Monad (foldM)
import           Control.Monad.IO.Class (liftIO)
import           Data.IORef (IORef, modifyIORef)
import           Data.Maybe (mapMaybe, fromMaybe)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl), testEquality)

import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

-- parameterized-utils
import           Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (ixF')
import           Data.Parameterized.Some (Some(Some))

-- what4
import qualified What4.Interface as What4
import           What4.FunctionName (functionName)
import           What4.ProgramLoc (ProgramLoc)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.FunctionHandle (SomeHandle(..), handleMapToHandles, handleName)
import           Lang.Crucible.Simulator.ExecutionTree (functionBindings, stateContext, fnBindings)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Override
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, MemImpl, MemOptions)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation, transContext, llvmTypeCtx, llvmDeclToFunHandleRepr')
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Intrinsics (LLVMOverride(..), basic_llvm_override)

import           Crux.Types (OverM)

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Constraints (ConstrainedTypedValue(..), minimalConstrainedShape, ConstrainedShape)
import           UCCrux.LLVM.Context.Module (ModuleContext, funcTypes, moduleTypes, moduleDecls)
import           UCCrux.LLVM.Cursor (Selector(..), Cursor(..), deepenPtr, seekType)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(SometimesClobber, ClobberGlobal))
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType, testCompatibility)
import           UCCrux.LLVM.FullType.Translation (FunctionTypes, ftRetType)
import           UCCrux.LLVM.FullType.Type (ModuleTypes, FullType(FTPtr), FullTypeRepr(..), ToCrucibleType, pointedToType)
import qualified UCCrux.LLVM.Mem as Mem
import           UCCrux.LLVM.Module (GlobalSymbol, FuncSymbol, funcSymbol, makeFuncSymbol, isDebug, funcSymbolToString)
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
-- This won't register overrides for functions that already have associated
-- CFGs, like if you already registered a normal override for `free` or similar.
unsoundSkipOverrides ::
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  ModuleContext m arch ->
  sym ->
  ModuleTranslation arch ->
  -- | Set of skip overrides encountered during execution
  IORef (Set SkipOverrideName) ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | What data should get clobbered by this override?
  Map (FuncSymbol m) (ClobberSpecs m) ->
  -- | Postconditions of each override (constraints on return values)
  Map (FuncSymbol m) (ConstrainedTypedValue m) ->
  [L.Declare] ->
  OverM personality sym LLVM [Either (ClobberSpecError m) (PolymorphicLLVMOverride arch (personality sym) sym)]
unsoundSkipOverrides modCtx sym mtrans usedRef annotationRef clobbers postconditions decls =
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
                (fromMaybe emptyClobberSpecs $ Map.lookup funcSym clobbers)
                (Map.lookup funcSym postconditions)
                funcSym
    pure $
      mapMaybe
        create
        ( filter
            ((`Set.notMember` alreadyDefined) . declName)
            (filter (not . isDebug) decls)
        )

-- | A 'ClobberSelector' points to a spot inside an argument or global variable
data ClobberSelector m (argTypes :: Ctx (FullType m)) inTy atTy
  = ClobberSelectArgument !(Ctx.Index argTypes inTy) (Cursor m inTy atTy)
  | ClobberSelectGlobal !(GlobalSymbol m) (Cursor m inTy atTy)
  deriving Eq

_clobberSelectorToSelector ::
  ClobberSelector m argTypes inTy atTy ->
  Selector m argTypes inTy atTy
_clobberSelectorToSelector =
  \case
    ClobberSelectArgument idx cursor -> SelectArgument idx cursor
    ClobberSelectGlobal glob cursor -> SelectGlobal glob cursor

clobberSelectorCursor ::
  ClobberSelector m argTypes inTy atTy ->
  Cursor m inTy atTy
clobberSelectorCursor =
  \case
    ClobberSelectArgument _idx cursor -> cursor
    ClobberSelectGlobal _glob cursor -> cursor

-- | What data should this override clobber?
--
-- These specs can explicitly set a type of data to generate (@argTypes@,
-- @inTy@, @atTy@), which may or may not actually match the declared type of the
-- data in question. This is useful for clobbering e.g. a @char*@ or @void*@
-- with structured data. However, it yields some API and implementation
-- complexity due to possible type mismatches (see 'ClobberSpecError').
data ClobberSpec m (argTypes :: Ctx (FullType m)) inTy atTy
  = ClobberSpec
      { clobberSelector :: ClobberSelector m argTypes inTy ('FTPtr atTy),
        -- | Type of value that contains the pointer
        clobberType :: FullTypeRepr m inTy,
        -- | Constraints on data to write
        clobberShape :: ConstrainedShape m atTy
      }
  deriving Eq

data SomeClobberSpec m
  = forall (argTypes :: Ctx (FullType m)) inTy atTy.
      SomeClobberSpec (ClobberSpec m argTypes inTy atTy)

data ClobberSpecError m
  = ClobberMismatchedSize !(FuncSymbol m)
  | ClobberMismatchedType !(FuncSymbol m)
  deriving (Eq, Ord)

ppClobberSpecError :: ClobberSpecError m -> PP.Doc ann
ppClobberSpecError =
  \case
    ClobberMismatchedSize f ->
      PP.hsep
        [ "Specification for values clobbered by the skipped function",
          PP.pretty (funcSymbolToString f),
          "included an argument index that is out of range for that function."
        ]
    ClobberMismatchedType f ->
      PP.hsep
        [ "Specification for values clobbered by the skipped function",
          PP.pretty (funcSymbolToString f),
          "included a value that was ill-typed with respect to that function's",
          "arguments."
        ]

-- | Retrieve the value specified by a 'ClobberSelector'.
--
-- 'makeGetter' returns this sort of callback because we want to produce
-- 'ClobberSpecError's statically, that is, before executing the override, and
-- this is a relatively simple way to encapsulate the type information learned
-- by GADT case splits in 'makeGetter'.
newtype ClobberGetter arch args inTy =
  ClobberGetter
    { getClobberGetter ::
        forall sym.
        MemImpl sym ->
        Ctx.Assignment (Crucible.RegEntry sym) args ->
        IO (Crucible.RegValue sym (ToCrucibleType arch inTy))
    }

-- | Retrieve a getter for the value with the pointer to be clobbered.
--
-- See comment on 'ClobberGetter'.
makeGetter ::
  forall proxy m arch args argTypes inTy atTy.
  ArchOk arch =>
  proxy arch ->
  FuncSymbol m ->
  Ctx.Assignment CrucibleTypes.TypeRepr args ->
  ClobberSpec m argTypes inTy atTy ->
  Either (ClobberSpecError m) (ClobberGetter arch args inTy)
makeGetter proxy funcSymb argTys spec = go (clobberType spec) (clobberSelector spec)
  where
    go ::
      FullTypeRepr m inTy ->
      ClobberSelector m argTypes inTy ('FTPtr atTy) ->
      Either (ClobberSpecError m) (ClobberGetter arch args inTy)
    go ftRepr =
      \case
        ClobberSelectArgument idx _ ->
          case Ctx.intIndex (Ctx.indexVal idx) (Ctx.size argTys) of
            Nothing -> Left (ClobberMismatchedSize funcSymb)
            Just (Some idx') ->
              let ty = argTys ^. ixF' idx'
              in case testCompatibility proxy ftRepr ty of
                  Nothing -> Left (ClobberMismatchedType funcSymb)
                  Just Refl ->
                    Right $
                      ClobberGetter $
                        \_mem args ->
                          return (args ^. ixF' idx' . to Crucible.regValue)
        ClobberSelectGlobal _glob _cursor ->
          unimplemented "makeGetter" ClobberGlobal

clobberAtType ::
  ModuleTypes m ->
  ClobberSpec m argTypes inTy atTy ->
  FullTypeRepr m atTy
clobberAtType modTys spec =
  pointedToType
    modTys
    (seekType
      modTys
      (clobberSelectorCursor (clobberSelector spec))
      (clobberType spec))

-- | When and where should this override clobber its arguments or globals?
data ClobberSpecs' m a
  = ClobberSpecs
      { -- | Stuff to clobber at each call
        alwaysClobber :: [a],
        -- | Stuff to clobber at particular callsites
        clobberAt :: Map ProgramLoc [a]
      }

type ClobberSpecs m = ClobberSpecs' m (SomeClobberSpec m)

makeClobberSpecs ::
  -- | Stuff to clobber at each call
  [SomeClobberSpec m] ->
  -- | Stuff to clobber at particular callsites
  Map ProgramLoc [SomeClobberSpec m] ->
  ClobberSpecs m
makeClobberSpecs = ClobberSpecs

emptyClobberSpecs :: ClobberSpecs' m a
emptyClobberSpecs =
  ClobberSpecs { alwaysClobber = mempty, clobberAt = mempty }

-- | Left-biased union
instance Semigroup (ClobberSpecs' m a) where
  cs1 <> cs2 =
    ClobberSpecs
      { alwaysClobber = alwaysClobber cs1 <> alwaysClobber cs2,
        clobberAt = clobberAt cs1 <> clobberAt cs2
      }

instance Monoid (ClobberSpecs' m a) where
  mempty = emptyClobberSpecs

-- | @args@ and @argTypes@ are not necessarily related, see comment on
-- 'ClobberGetter'.
data SomeClobberSpecAndGetter m arch args
  = forall (argTypes :: Ctx (FullType m)) inTy atTy.
      SomeClobberSpecAndGetter
        (ClobberSpec m argTypes inTy atTy)
        (ClobberGetter arch args inTy)

makeGetters ::
  ArchOk arch =>
  proxy arch ->
  FuncSymbol m ->
  Ctx.Assignment CrucibleTypes.TypeRepr args ->
  ClobberSpecs m ->
  Either (ClobberSpecError m) (ClobberSpecs' m (SomeClobberSpecAndGetter m arch args))
makeGetters proxy funcSymb args specs =
  ClobberSpecs
  <$> traverse mk (alwaysClobber specs)
  <*> traverse (traverse mk) (clobberAt specs)
  where mk (SomeClobberSpec spec) =
          SomeClobberSpecAndGetter spec <$> makeGetter proxy funcSymb args spec


-- | Create an override that takes the place of a given defined or even
-- declared/external function, and instead of executing that function,
-- instead manufactures a fresh symbolic return value and optionally clobbers
-- some parts of its arguments or global variables with fresh symbolic values.
--
-- Useful for continuing symbolic execution in the presence of external/library
-- functions.
createSkipOverride ::
  forall m arch sym argTypes personality.
  ( IsSymInterface sym,
    HasLLVMAnn sym,
    ArchOk arch,
    ?lc :: TypeContext,
    ?memOpts :: MemOptions
  ) =>
  ModuleContext m arch ->
  sym ->
  IORef (Set SkipOverrideName) ->
  -- | Annotations of created values
  IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
  -- | What data should get clobbered by this override?
  ClobberSpecs m ->
  -- | Constraints on the return value
  Maybe (ConstrainedTypedValue m) ->
  -- | Function to be overridden
  FuncSymbol m ->
  Maybe (Either (ClobberSpecError m) (PolymorphicLLVMOverride arch (personality sym) sym))
createSkipOverride modCtx sym usedRef annotationRef clobbers postcondition funcSymb =
  llvmDeclToFunHandleRepr' decl $
    \argTys retTy ->
      Just $
        case makeGetters modCtx funcSymb argTys clobbers of
          Left err -> Left err
          Right clobbers' ->
            Right $
              makePolymorphicLLVMOverride $
                basic_llvm_override $
                  LLVMOverride
                    { llvmOverride_declare = decl,
                      llvmOverride_args = argTys,
                      llvmOverride_ret = retTy,
                      llvmOverride_def =
                        \mvar _sym args ->
                          do
                            liftIO $
                              modifyIORef usedRef (Set.insert (SkipOverrideName name))
                            Override.modifyGlobal mvar $
                              \mem ->
                                liftIO $
                                  do mem' <- applyClobbers mem args clobbers'
                                     returnValue
                                       mem'
                                       retTy
                                       (modCtx ^. funcTypes . funcSymbol funcSymb)
                    }
  where
    decl = modCtx ^. moduleDecls . funcSymbol funcSymb
    name = declName decl
    symbolName = L.decName decl

    clobberOne ::
      MemImpl sym ->
      Ctx.Assignment (Crucible.RegEntry sym) args ->
      ClobberSpec m args' inTy atTy ->
      ClobberGetter arch args inTy ->
      IO (MemImpl sym)
    clobberOne mem args spec getter =
      do let mts = modCtx ^. moduleTypes
         (result, value) <-
           runSetup
             modCtx
             mem
             ( generate
                 sym
                 modCtx
                 (clobberAtType mts spec)
                 (SelectClobbered
                    funcSymb
                    (deepenPtr mts (clobberSelectorCursor (clobberSelector spec))))
                 (clobberShape spec)
             )
         assume name sym (resultAssumptions result)
         -- The keys are nonces, so they'll never clash, so the
         -- bias of the union is unimportant.
         modifyIORef annotationRef (Map.union (resultAnnotations result))
         container <- getClobberGetter getter mem args
         let cursor = clobberSelectorCursor (clobberSelector spec)
         ptr <- Mem.seekPtr modCtx sym mem (clobberType spec) container cursor
         let mem' = resultMem result
         let val = value ^. Shape.tag . to getSymValue
         Mem.store modCtx sym mem' (clobberAtType mts spec) ptr val

    applyClobbers ::
      MemImpl sym ->
      Ctx.Assignment (Crucible.RegEntry sym) args ->
      ClobberSpecs' m (SomeClobberSpecAndGetter m arch args) ->
      IO (MemImpl sym)
    applyClobbers mem args clobbers' =
      if not (Map.null (clobberAt clobbers'))
      then unimplemented "doClobber" SometimesClobber
      else
        foldM
          (\mem' (SomeClobberSpecAndGetter spec getter) ->
             clobberOne mem' args spec getter)
          mem
          (alwaysClobber clobbers')

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
              do (result, value) <-
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
                 assume name sym (resultAssumptions result)
                 -- The keys are nonces, so they'll never clash, so the
                 -- bias of the union is unimportant.
                 modifyIORef annotationRef (Map.union (resultAnnotations result))
                 pure (value ^. Shape.tag . to getSymValue, resultMem result)
