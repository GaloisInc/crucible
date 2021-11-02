{-
Module           : UCCrux.LLVM.Module
Description      : LLVM module wrapper with type-level evidence.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module provides a mechanism for generating fresh type-level names for LLVM
modules, a la justified-containers. These names can be associated with symbols
in the module (such as global variables and functions), which can later be
looked up without introducing partiality (@Maybe@).
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Module
  ( -- * Maps
    DeclSymbol,
    DeclMap,
    DefnSymbol,
    DefnMap,
    FuncSymbol(..),
    FuncMap(..),
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

    -- * Module

    Module,
    getModule,
    makeSomeModule,
    isDebug,
    moduleDeclMap,
    moduleDefnMap,
    moduleGlobalMap,
    allModuleDeclMap,
  )
where

import           Control.Lens.At (At(at), Ixed(ix), Index, IxValue, ixAt)
import           Control.Lens (Simple, Lens, Lens', lens)
import           Control.Lens.Indexed (FunctorWithIndex(imap), FoldableWithIndex(ifoldMap))
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)

import qualified Prettyprinter as PP

import qualified Text.LLVM as L

import           Data.Parameterized.Some (Some(Some))

import           Lang.Crucible.LLVM.MalformedLLVMModule (malformedLLVMModule)
import           Lang.Crucible.LLVM.Translation (declareFromDefine)

import           UCCrux.LLVM.Errors.Panic (panic)

--------------------------------------------------------------------------------
-- Maps

-- | Type level only, should probably not get exported in order to preserve the
-- opacity of the representation of 'DeclSymbol' and friends.
data SymbolType
  = Decl
  | Defn
  | Global

-- | A name of a function or global from a specific LLVM module.
--
-- Should probably not get exported in order to preserve the opacity of the
-- representation of 'DeclSymbol' and friends.
newtype Symbol m (t :: SymbolType) = Symbol {_getSymbol :: L.Symbol}
  deriving (Eq, Ord)

-- | Constructor not exported to preserve opacity of representation.
newtype DeclSymbol m = DeclSymbol
  {runDeclSymbol :: Symbol m 'Decl}
  deriving (Eq, Ord)

-- | Constructor not exported to preserve opacity of representation.
newtype DefnSymbol m = DefnSymbol
  {runDefnSymbol :: Symbol m 'Defn}
  deriving (Eq, Ord)

-- | Constructor not exported to preserve opacity of representation.
newtype GlobalSymbol m = GlobalSymbol
  {runGlobalSymbol :: Symbol m 'Global}
  deriving (Eq, Ord)

-- | Constructor not exported to preserve opacity of representation.
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

data FuncSymbol m
  = FuncDeclSymbol (DeclSymbol m)
  | FuncDefnSymbol (DefnSymbol m)
  deriving (Eq, Ord)

type instance Index (FuncMap m a) = FuncSymbol m

type instance IxValue (FuncMap m a) = a

instance FunctorWithIndex (FuncSymbol m) (FuncMap m) where
  imap f (FuncMap decls defns) =
    FuncMap
      { _funcMapDecls =
          imap
            (\sym val -> f (FuncDeclSymbol sym) val)
            decls,
        _funcMapDefns =
          imap
            (\sym val -> f (FuncDefnSymbol sym) val)
            defns
      }


instance FoldableWithIndex (FuncSymbol m) (FuncMap m) where
  ifoldMap f (FuncMap decls defns) =
    ifoldMap
      (\sym val -> f (FuncDeclSymbol sym) val)
      decls
      <> ifoldMap
           (\sym val -> f (FuncDefnSymbol sym) val)
           defns

instance At (FuncMap m a) where
  at =
    \case
      FuncDeclSymbol declSymb -> funcMapDecls . at declSymb
      FuncDefnSymbol defnSymb -> funcMapDefns . at defnSymb

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
    (Just declSymb, Nothing) -> Just (FuncDeclSymbol declSymb)
    (Nothing, Just defnSymb) -> Just (FuncDefnSymbol defnSymb)
    (Nothing, Nothing) -> Nothing
    (Just {}, Just {}) ->
      malformedLLVMModule
        "Function both declared and defined"
        ["Function name:" <> PP.pretty name]

funcSymbol :: FuncSymbol m -> Lens' (FuncMap m a) a
funcSymbol =
  \case
    FuncDeclSymbol declSymb -> funcMapDecls . declSymbol declSymb
    FuncDefnSymbol defnSymb -> funcMapDefns . defnSymbol defnSymb

getFuncSymbol :: FuncSymbol m -> L.Symbol
getFuncSymbol =
  \case
    FuncDeclSymbol declSymb -> getDeclSymbol declSymb
    FuncDefnSymbol defnSymb -> getDefnSymbol defnSymb

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
   in GlobalSymbol gs <$ Map.lookup gs mp

getGlobalSymbol :: GlobalSymbol m -> L.Symbol
getGlobalSymbol (GlobalSymbol (Symbol s)) = s

isEmptyGlobalMap :: GlobalMap m a -> Bool
isEmptyGlobalMap (GlobalMap (SymbolMap m)) = Map.null m

--------------------------------------------------------------------------------
-- Module

-- | An LLVM module identified by the phantom type parameter @m@. Constructor
-- must not be exported.
newtype Module m = Module { getModule :: L.Module }
  deriving (Eq, Ord, Show)

-- | Invent a fresh type-level name for this LLVM module.
makeSomeModule :: L.Module -> Some Module
makeSomeModule = Some . Module

-- | Debug intrinsics don't have their types translated because
--
-- * It's not necessary - overrides for these are installed as part of
--   crucible-llvm's default set for LLVM intrinsics.
-- * 'FullType' doesn\'t have a notion of metadata type, and it\'s nice to keep
--   it that way to avoid a bunch of spurrious/impossible cases elsewhere.
isDebug :: L.Declare -> Bool
isDebug = ("llvm.dbg" `List.isPrefixOf`) . getNm . L.decName
  where
    getNm (L.Symbol nm) = nm

-- | This function will exclude debug intrinsics because debug types are not yet
-- supported.
moduleDeclMap :: Module m -> DeclMap m L.Declare
moduleDeclMap (Module m) =
  DeclMap
    (SymbolMap
      (Map.fromList
        [(Symbol (L.decName decl), decl) | decl <- L.modDeclares m, not (isDebug decl)]))

moduleDefnMap :: Module m -> DefnMap m L.Define
moduleDefnMap (Module m) =
  DefnMap
    (SymbolMap
      (Map.fromList
        [(Symbol (L.defName defn), defn) | defn <- L.modDefines m]))

moduleGlobalMap :: Module m -> GlobalMap m L.Global
moduleGlobalMap (Module m) =
  GlobalMap
    (SymbolMap
      (Map.fromList
        [(Symbol (L.globalSym glob), glob) | glob <- L.modGlobals m]))

-- | A map of declarations for every declaration and definition in the module.
--
-- This function will exclude debug intrinsics because debug types are not yet
-- supported.
allModuleDeclMap :: Module m -> FuncMap m L.Declare
allModuleDeclMap m =
  makeFuncMap
    (moduleDeclMap m)
    (fmap declareFromDefine (moduleDefnMap m))
