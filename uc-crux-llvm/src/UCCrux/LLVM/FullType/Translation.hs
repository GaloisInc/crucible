{-
Module           : UCCrux.LLVM.FullType.Translation
Description      : Translation
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.Translation
  ( -- * Maps
    DeclSymbol,
    DeclMap,
    DefnSymbol,
    DefnMap,
    FuncSymbol(..),
    FuncMap,
    GlobalSymbol,
    GlobalMap,
    declSymbol,
    makeDeclSymbol,
    getDeclSymbol,
    isEmptyDeclMap,
    defnSymbol,
    makeDefnSymbol,
    getDefnSymbol,
    isEmptyDefnMap,
    makeFuncMap,
    funcMapDecls,
    funcMapDefns,
    makeFuncSymbol,
    funcSymbol,
    getFuncSymbol,
    globalSymbol,
    makeGlobalSymbol,
    getGlobalSymbol,
    isEmptyGlobalMap,

    -- * Translation
    FunctionTypes (..),
    MatchingAssign (..),
    TranslatedTypes (..),
    TypeTranslationError (..),
    isDebug,
    translateModuleDefines,
    ppTypeTranslationError,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (unzip)

import           Control.Lens.At (At(at), Ixed(ix), Index, IxValue, ixAt)
import           Control.Lens (Simple, Lens, Lens', lens)
import           Control.Lens.Indexed (FunctorWithIndex(imap), FoldableWithIndex(ifoldMap))
import           Control.Monad (unless)
import           Control.Monad.Except (ExceptT, runExceptT, throwError, withExceptT)
import           Control.Monad.State (State, runState)
import           Data.Functor ((<&>))
import qualified Data.List as List
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           Lang.Crucible.LLVM.MalformedLLVMModule (malformedLLVMModule)
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

--------------------------------------------------------------------------------
-- Maps

-- | Type level only
data SymbolType
  = Decl
  | Defn
  | Global

-- | A name of a function or global from a specific LLVM module
newtype Symbol m (t :: SymbolType) = Symbol {_getSymbol :: L.Symbol}
  deriving (Eq, Ord)

newtype DeclSymbol m = DeclSymbol
  {runDeclSymbol :: Symbol m 'Decl}
  deriving (Eq, Ord)

newtype DefnSymbol m = DefnSymbol
  {runDefnSymbol :: Symbol m 'Defn}
  deriving (Eq, Ord)

newtype GlobalSymbol m = GlobalSymbol
  {runGlobalSymbol :: Symbol m 'Global}
  deriving (Eq, Ord)

newtype SymbolMap m t a = SymbolMap
  {getSymbolMap :: Map (Symbol m t) a}
  deriving (Foldable, Functor, Traversable)

type instance Index (SymbolMap m t a) = Symbol m t

type instance IxValue (SymbolMap m t a) = a

-- Not sure why these can't be derived?
instance FunctorWithIndex (Symbol m t) (SymbolMap m t) where
  imap f (SymbolMap m) = SymbolMap (imap f m)

instance FoldableWithIndex (Symbol m t) (SymbolMap m t) where
  ifoldMap f (SymbolMap m) = ifoldMap f m

instance At (SymbolMap m t a) where
  at symb = lens getSymbolMap (const SymbolMap) . at symb

instance Ixed (SymbolMap m t a) where
  ix = ixAt

-- | Constructor not exported to enforce the invariant that a 'DeclMap'
-- holds a value for every LLVM function declaration in the corresponding module
-- indicated by the @m@ parameter.
newtype DeclMap m a = DeclMap
  {getDeclMap :: SymbolMap m 'Decl a}
  deriving (Foldable, Functor, Traversable)

type instance Index (DeclMap m a) = DeclSymbol m

type instance IxValue (DeclMap m a) = a

instance FunctorWithIndex (DeclSymbol m) (DeclMap m) where
  imap f (DeclMap m) =
    DeclMap (imap (\sym val -> f (DeclSymbol sym) val) m)

instance FoldableWithIndex (DeclSymbol m) (DeclMap m) where
  ifoldMap f (DeclMap m) =
    ifoldMap (\sym val -> f (DeclSymbol sym) val) m

instance At (DeclMap m a) where
  at symb = lens getDeclMap (const DeclMap) . at (runDeclSymbol symb)

instance Ixed (DeclMap m a) where
  ix = ixAt

-- | Constructor not exported to enforce the invariant that a 'DefnMap'
-- holds a value for every LLVM function definition in the corresponding module
-- indicated by the @m@ parameter.
newtype DefnMap m a = DefnMap
  {getDefnMap :: SymbolMap m 'Defn a}
  deriving (Foldable, Functor, Traversable)

type instance Index (DefnMap m a) = DefnSymbol m

type instance IxValue (DefnMap m a) = a

instance FunctorWithIndex (DefnSymbol m) (DefnMap m) where
  imap f (DefnMap m) =
    DefnMap (imap (\sym val -> f (DefnSymbol sym) val) m)

instance FoldableWithIndex (DefnSymbol m) (DefnMap m) where
  ifoldMap f (DefnMap m) =
    ifoldMap (\sym val -> f (DefnSymbol sym) val) m

instance At (DefnMap m a) where
  at symb = lens getDefnMap (const DefnMap) . at (runDefnSymbol symb)

instance Ixed (DefnMap m a) where
  ix = ixAt

-- | A map containing values for function declarations and definitions in an
-- LLVM module.
data FuncMap m a = FuncMap
  { _funcMapDecls :: DeclMap m a,
    _funcMapDefns :: DefnMap m a
  }
  deriving (Foldable, Functor, Traversable)

funcMapDecls :: Simple Lens (FuncMap m a) (DeclMap m a)
funcMapDecls = lens _funcMapDecls (\s v -> s { _funcMapDecls = v })

funcMapDefns :: Simple Lens (FuncMap m a) (DefnMap m a)
funcMapDefns = lens _funcMapDefns (\s v -> s { _funcMapDefns = v })

makeFuncMap :: DeclMap m a -> DefnMap m a -> FuncMap m a
makeFuncMap = FuncMap

newtype FuncSymbol m =
  FuncSymbol { runFuncSymbol :: Either (DeclSymbol m) (DefnSymbol m) }
  deriving (Eq, Ord)

type instance Index (FuncMap m a) = FuncSymbol m

type instance IxValue (FuncMap m a) = a

instance FunctorWithIndex (FuncSymbol m) (FuncMap m) where
  imap f (FuncMap decls defns) =
    FuncMap
      { _funcMapDecls =
          imap
            (\sym val -> f (FuncSymbol (Left sym)) val)
            decls,
        _funcMapDefns =
          imap
            (\sym val -> f (FuncSymbol (Right sym)) val)
            defns
      }


instance FoldableWithIndex (FuncSymbol m) (FuncMap m) where
  ifoldMap f (FuncMap decls defns) =
    ifoldMap
      (\sym val -> f (FuncSymbol (Left sym)) val)
      decls
      <> ifoldMap
           (\sym val -> f (FuncSymbol (Right sym)) val)
           defns

instance At (FuncMap m a) where
  at symb =
    case runFuncSymbol symb of
      Left declSymb -> funcMapDecls . at declSymb
      Right defnSymb -> funcMapDefns . at defnSymb

instance Ixed (FuncMap m a) where
  ix = ixAt

-- | Constructor not exported to enforce the invariant that a 'GlobalMap' holds
-- a value for every LLVM global in the corresponding module indicated by the
-- @m@ parameter.
newtype GlobalMap m a = GlobalMap
  {getGlobalMap :: SymbolMap m 'Global a}
  deriving (Foldable, Functor, Traversable)

type instance Index (GlobalMap m a) = GlobalSymbol m

type instance IxValue (GlobalMap m a) = a

instance FunctorWithIndex (GlobalSymbol m) (GlobalMap m) where
  imap f (GlobalMap m) =
    GlobalMap (imap (\sym val -> f (GlobalSymbol sym) val) m)

instance FoldableWithIndex (GlobalSymbol m) (GlobalMap m) where
  ifoldMap f (GlobalMap m) =
    ifoldMap (\sym val -> f (GlobalSymbol sym) val) m

instance At (GlobalMap m a) where
  at symb = lens getGlobalMap (const GlobalMap) . at (runGlobalSymbol symb)

instance Ixed (GlobalMap m a) where
  ix = ixAt

declSymbol :: DeclSymbol m -> Lens' (DeclMap m a) a
declSymbol (DeclSymbol sym) =
  lens
    ( fromMaybe
        ( panic
            "declSymbol"
            ["Broken invariant: DeclSymbol not present in DeclMap"]
        )
        . Map.lookup sym
        . getSymbolMap
        . getDeclMap
    )
    (\(DeclMap (SymbolMap m)) a -> DeclMap (SymbolMap (Map.insert sym a m)))

makeDeclSymbol :: L.Symbol -> DeclMap m a -> Maybe (DeclSymbol m)
makeDeclSymbol symbol (DeclMap (SymbolMap mp)) =
  let gs = Symbol symbol
   in case Map.lookup gs mp of
        Just _ -> Just (DeclSymbol gs)
        Nothing -> Nothing

getDeclSymbol :: DeclSymbol m -> L.Symbol
getDeclSymbol (DeclSymbol (Symbol s)) = s

isEmptyDeclMap :: DeclMap m a -> Bool
isEmptyDeclMap (DeclMap (SymbolMap m)) = Map.null m

defnSymbol :: DefnSymbol m -> Lens' (DefnMap m a) a
defnSymbol (DefnSymbol sym) =
  lens
    ( fromMaybe
        ( panic
            "defnSymbol"
            ["Broken invariant: DefnSymbol not present in DefnMap"]
        )
        . Map.lookup sym
        . getSymbolMap
        . getDefnMap
    )
    (\(DefnMap (SymbolMap m)) a -> DefnMap (SymbolMap (Map.insert sym a m)))

makeDefnSymbol :: L.Symbol -> DefnMap m a -> Maybe (DefnSymbol m)
makeDefnSymbol symbol (DefnMap (SymbolMap mp)) =
  let gs = Symbol symbol
   in case Map.lookup gs mp of
        Just _ -> Just (DefnSymbol gs)
        Nothing -> Nothing

getDefnSymbol :: DefnSymbol m -> L.Symbol
getDefnSymbol (DefnSymbol (Symbol s)) = s

isEmptyDefnMap :: DefnMap m a -> Bool
isEmptyDefnMap (DefnMap (SymbolMap m)) = Map.null m

makeFuncSymbol :: L.Symbol -> FuncMap m a -> Maybe (FuncSymbol m)
makeFuncSymbol symbol@(L.Symbol name) (FuncMap decls defns) =
  case ( makeDeclSymbol symbol decls,
         makeDefnSymbol symbol defns
       ) of
    (Just declSymb, Nothing) -> Just (FuncSymbol (Left declSymb))
    (Nothing, Just defnSymb) -> Just (FuncSymbol (Right defnSymb))
    (Nothing, Nothing) -> Nothing
    (Just {}, Just {}) ->
      malformedLLVMModule
        "Function both declared and defined"
        ["Function name:" <> PP.pretty name]

funcSymbol :: FuncSymbol m -> Lens' (FuncMap m a) a
funcSymbol =
  \case
    FuncSymbol (Left declSymb) -> funcMapDecls . declSymbol declSymb
    FuncSymbol (Right defnSymb) -> funcMapDefns . defnSymbol defnSymb

getFuncSymbol :: FuncSymbol m -> L.Symbol
getFuncSymbol = either getDeclSymbol getDefnSymbol . runFuncSymbol

globalSymbol :: GlobalSymbol m -> Lens' (GlobalMap m a) a
globalSymbol (GlobalSymbol sym) =
  lens
    ( fromMaybe
        ( panic
            "globalSymbol"
            ["Broken invariant: GlobalSymbol not present in GlobalMap"]
        )
        . Map.lookup sym
        . getSymbolMap
        . getGlobalMap
    )
    (\(GlobalMap (SymbolMap m)) a -> GlobalMap (SymbolMap (Map.insert sym a m)))

makeGlobalSymbol :: GlobalMap m a -> L.Symbol -> Maybe (GlobalSymbol m)
makeGlobalSymbol (GlobalMap (SymbolMap mp)) symbol =
  let gs = Symbol symbol
   in case Map.lookup gs mp of
        Just _ -> Just (GlobalSymbol gs)
        Nothing -> Nothing

getGlobalSymbol :: GlobalSymbol m -> L.Symbol
getGlobalSymbol (GlobalSymbol (Symbol s)) = s

isEmptyGlobalMap :: GlobalMap m a -> Bool
isEmptyGlobalMap (GlobalMap (SymbolMap m)) = Map.null m

--------------------------------------------------------------------------------
-- Translation

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
data TranslatedTypes arch = forall m.
  TranslatedTypes
  { translatedModuleTypes :: ModuleTypes m,
    translatedGlobalTypes :: GlobalMap m (Some (FullTypeRepr m)),
    translatedDeclTypes :: FuncMap m (FunctionTypes m arch)
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
                  (,,)
                    <$> mapM
                          translateDeclare
                          ( filter
                              (not . isDebug)
                              (L.modDeclares llvmModule)
                          )
                    <*> mapM translateDefine (L.modDefines llvmModule)
                    <*> mapM translateGlobal (L.modGlobals llvmModule)
              )
              initialModuleTypes
       in maybeResult
            <&> \(declTypes, defnTypes, globalTypes) ->
              TranslatedTypes
                modTypes
                (GlobalMap (SymbolMap (Map.fromList globalTypes)))
                (FuncMap
                  (DeclMap (SymbolMap (Map.fromList declTypes)))
                  (DefnMap (SymbolMap (Map.fromList defnTypes))))
  where
    translateGlobal ::
      L.Global ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (Symbol m 'Global, Some (FullTypeRepr m))
    translateGlobal glob =
      do
        memTy <- withExceptT BadLift (LLVMTrans.liftMemType (L.globalType glob))
        ty <- withExceptT FullTypeTranslation (toFullTypeM memTy)
        pure (Symbol (L.globalSym glob), ty)

    translateDefine ::
      L.Define ->
      ExceptT
        TypeTranslationError
        (State (ModuleTypes m))
        (Symbol m 'Defn, FunctionTypes m arch)
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
              ( Symbol (L.decName decl),
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
        (Symbol m 'Decl, FunctionTypes m arch)
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
          ( Symbol (L.decName decl),
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
