------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Globals
-- Description      : Operations for working with LLVM global variables
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides support for dealing with LLVM global variables,
-- including initial allocation and populating variables with their
-- initial values.  A @GlobalInitializerMap@ is constructed during
-- module translation and can subsequently be used to populate
-- global variables.  This can either be done all at once using
-- @populateAllGlobals@; or it can be done in a more selective manner,
-- using one of the other \"populate\" operations.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

module Lang.Crucible.LLVM.Globals
  ( initializeMemory
  , populateGlobal
  , populateGlobals
  , populateAllGlobals
  , populateConstGlobals

  , GlobalInitializerMap
  , makeGlobalMap
  ) where

import Control.Arrow ((>>>), (&&&))
import Control.Monad.Except
import Control.Lens hiding (op, (:>) )
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as LPP

import           Data.Parameterized.NatRepr as NatRepr

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Intrinsics
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Translation.Types

import           Lang.Crucible.Backend (IsSymInterface)

------------------------------------------------------------------------
-- GlobalInitializerMap

-- | A @GlobalInitializerMap@ records the initialized values of globals in an @L.Module@.
--
-- The @Left@ constructor is used to signal errors in translation,
-- which can happen when:
-- * The global isn't actually a compile-time constant
-- * The declaration is ill-typed
-- * The global isn't linked ("extern global")
--
-- These failures are as granular as possible (attached to the values)
-- so that simulation still succeeds if the module has a bad global that the
-- verified function never touches.
--
-- To actually initialize globals, saw-script translates them into
-- instances of @MemModel.LLVMVal@.
type GlobalInitializerMap = Map L.Symbol (L.Global, Either String (MemType, LLVMConst))


------------------------------------------------------------------------
-- makeGlobalMap

-- | Commute an applicative with Maybe
commuteMaybe :: Applicative n => Maybe (n a) -> n (Maybe a)
commuteMaybe (Just val) = Just <$> val
commuteMaybe Nothing    = pure Nothing

-- | Commute a functor with pairing
fSnd :: Functor n => (a, n b) -> n (a, b)
fSnd (a, nb) = fmap ((,) a) nb

-- | @makeGlobalMap@ creates a map from names of LLVM global variables
-- to the values of their initializers, if any are included in the module.
makeGlobalMap :: forall arch wptr. (HasPtrWidth wptr)
              => LLVMContext arch
              -> L.Module
              -> GlobalInitializerMap
makeGlobalMap ctx m =
     Map.fromList $ map (L.globalSym &&& (id &&& globalToConst)) (L.modGlobals m)
  where -- Catch the error from @transConstant@, turn it into @Either@
        globalToConst :: L.Global -> Either String (MemType, LLVMConst)
        globalToConst g =
          catchError
            (globalToConst' g >>=
              flip maybeToEither
                (List.intercalate " " $
                  [ "The global"
                  , showSymbol $ L.globalSym g
                  , "is declared"
                  , case L.modSourceName m of
                      Nothing   -> ""
                      Just name -> "in the module " ++ name
                  , "but was missing. Did you link all of the relevant .bc files"
                  , "together with `llvm-link'?"
                  ]))
            (\err -> Left $
              "Encountered error while processing global "
                ++ showSymbol (L.globalSym g)
                ++ ": "
                ++ err)
          where showSymbol sym =
                  show $ let ?config = LPP.Config False False False
                         in LPP.ppSymbol $ sym

        maybeToEither :: Maybe a -> b -> Either b a
        maybeToEither Nothing b  = Left b
        maybeToEither (Just a) _ = Right a

        -- This is the pipeline:
        -- L.Global
        -- ==> (L.Type, Maybe L.Value)
        -- ==> Maybe (L.Type, L.Value)
        -- ==> Maybe (L.Typed L.Value)
        -- ==> Maybe (m LLVMConst)
        -- ==> m     (Maybe LLVMConst)
        globalToConst' :: forall m. (MonadError String m)
                       => L.Global -> m (Maybe (MemType, LLVMConst))
        globalToConst' =
          let ?lc = ctx^.llvmTypeCtx -- implicitly passed to transConstant
          in (L.globalType &&& L.globalValue)
                >>> fSnd
                >>> fmap (uncurry L.Typed)
                >>> fmap transConstantWithType
                >>> commuteMaybe


-------------------------------------------------------------------------
-- initializeMemory

-- | Build the initial memory for an LLVM program.  Note, this process
-- allocates space for global variables, but does not set their
-- initial values.
initializeMemory
   :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
   => sym
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeMemory sym llvm_ctx m = do
   -- Create initial memory of appropriate endianness
   let ?lc = llvm_ctx^.llvmTypeCtx
   let dl = TyCtx.llvmDataLayout ?lc
   let endianness = dl^.intLayout
   mem0 <- emptyMem endianness
   -- Allocate function handles
   let handles = Map.assocs (_symbolMap llvm_ctx)
   mem <- foldM (allocLLVMHandleInfo sym) mem0 handles
   -- Allocate global values
   let gs = L.modGlobals m
   gs_alloc <- mapM (\g -> do
                        ty <- liftMemType $ L.globalType g
                        let sz = memTypeSize dl ty
                        return (L.globalSym g, sz))
                    gs
   allocGlobals sym gs_alloc mem


allocLLVMHandleInfo :: (IsSymInterface sym, HasPtrWidth wptr)
                    => sym
                    -> MemImpl sym
                    -> (L.Symbol, LLVMHandleInfo)
                    -> IO (MemImpl sym)
allocLLVMHandleInfo sym mem (symbol@(L.Symbol sym_str), LLVMHandleInfo _ h) =
  do (ptr, mem') <- doMallocHandle sym G.GlobalAlloc sym_str mem (SomeFnHandle h)
     return (registerGlobal mem' symbol ptr)


-- | Populate the globals mentioned in the given @GlobalInitializerMap@
--   provided they satisfy the given filter function.
populateGlobals ::
  ( ?lc :: TyCtx.LLVMContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymInterface sym ) =>
  (L.Global -> Bool)   {- ^ Filter function, globals that cause this to return true will be populated -} ->
  sym ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateGlobals select sym gimap mem0 = foldM f mem0 (Map.elems gimap)
  where
  f mem (gl, _) | not (select gl) = return mem
  f _   (_, Left msg)             = fail msg
  f mem (gl, Right (mty, cval))   = populateGlobal sym gl mty cval mem


-- | Populate all the globals mentioned in the given @GlobalInitializerMap@.
populateAllGlobals ::
  ( ?lc :: TyCtx.LLVMContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymInterface sym ) =>
  sym ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateAllGlobals = populateGlobals (const True)


-- | Populate only the constant global variables mentioned in the
--   given @GlobalInitializerMap@.
populateConstGlobals ::
  ( ?lc :: TyCtx.LLVMContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymInterface sym ) =>
  sym ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateConstGlobals = populateGlobals f
  where f = L.gaConstant . L.globalAttrs


-- | Write the value of the given LLVMConst into the given global variable.
--   This is intended to be used at initialization time, and will populate
--   even read-only global data.
populateGlobal ::
  ( ?lc :: TyCtx.LLVMContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymInterface sym ) =>
  sym ->
  L.Global ->
  MemType ->
  LLVMConst ->
  MemImpl sym ->
  IO (MemImpl sym)
populateGlobal sym gl mt cval mem =
  do let symb = L.globalSym gl 
     ty <- toStorableType mt
     ptr <- doResolveGlobal sym mem symb
     val <- constToLLVMVal sym mem cval
     storeConstRaw sym mem ptr ty val
