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
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

module Lang.Crucible.LLVM.Globals
  ( initializeMemory
  , initializeAllMemory
  , initializeMemoryConstGlobals
  , populateGlobal
  , populateGlobals
  , populateAllGlobals
  , populateConstGlobals

  , GlobalInitializerMap
  , makeGlobalMap
  ) where

import           Control.Arrow ((&&&))
import           Control.Monad.Except
import           Control.Lens hiding (op, (:>) )
import           Data.List (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.String
import           Control.Monad.State (StateT, runStateT, get, put)
import           Data.Maybe (fromMaybe)

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as LPP

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.NatRepr as NatRepr

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.Backend (IsSymInterface)

import           What4.Interface

import           GHC.Stack

------------------------------------------------------------------------
-- GlobalInitializerMap

-- | A @GlobalInitializerMap@ records the initialized values of globals in an @L.Module@.
--
-- The @Left@ constructor is used to signal errors in translation,
-- which can happen when:
--  * The declaration is ill-typed
--  * The global isn't linked (@extern global@)
--
-- The @Nothing@ constructor is used to signal that the global isn't actually a
-- compile-time constant.
--
-- These failures are as granular as possible (attached to the values)
-- so that simulation still succeeds if the module has a bad global that the
-- verified function never touches.
--
-- To actually initialize globals, saw-script translates them into
-- instances of @MemModel.LLVMVal@.
type GlobalInitializerMap = Map L.Symbol (L.Global, Either String (MemType, Maybe LLVMConst))


------------------------------------------------------------------------
-- makeGlobalMap

-- | @makeGlobalMap@ creates a map from names of LLVM global variables
-- to the values of their initializers, if any are included in the module.
makeGlobalMap :: forall arch wptr. (?lc :: TypeContext, HasPtrWidth wptr)
              => LLVMContext arch
              -> L.Module
              -> GlobalInitializerMap
makeGlobalMap ctx m = foldl' addAliases globalMap (Map.toList (llvmGlobalAliases ctx))

  where
   addAliases mp (glob, aliases) =
        case Map.lookup glob mp of
          Just initzr -> insertAll (map L.aliasName (Set.toList aliases)) initzr mp
          Nothing     -> mp -- should this be an error/exception?

   globalMap = Map.fromList $ map (L.globalSym &&& (id &&& globalToConst))
                                  (L.modGlobals m)

   insertAll ks v mp = foldr (flip Map.insert v) mp ks

   -- Catch the error from @transConstant@, turn it into @Either@
   globalToConst :: L.Global -> Either String (MemType, Maybe LLVMConst)
   globalToConst g =
     catchError
       (globalToConst' g)
       (\err -> Left $
         "Encountered error while processing global "
           ++ showSymbol (L.globalSym g)
           ++ ": "
           ++ err)
     where showSymbol sym =
             show $ let ?config = LPP.Config False False False
                    in LPP.ppSymbol $ sym

   globalToConst' :: forall m. (MonadError String m)
                  => L.Global -> m (MemType, Maybe LLVMConst)
   globalToConst' g =
     do let ?lc  = ctx^.llvmTypeCtx -- implicitly passed to transConstant
        let gty  = L.globalType g
        let gval = L.globalValue g
        mt  <- liftMemType gty
        val <- traverse (transConstant' mt) gval
        return (mt, val)

-------------------------------------------------------------------------
-- initializeMemory

-- | Build the initial memory for an LLVM program.  Note, this process
-- allocates space for global variables, but does not set their
-- initial values.
initializeAllMemory
   :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
   => sym
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeAllMemory = initializeMemory (const True)

initializeMemoryConstGlobals
   :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
   => sym
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeMemoryConstGlobals = initializeMemory (L.gaConstant . L.globalAttrs)

initializeMemory
   :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
   => (L.Global -> Bool)
   -> sym
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeMemory predicate sym llvm_ctx m = do
   -- Create initial memory of appropriate endianness
   let ?lc = llvm_ctx^.llvmTypeCtx
   let dl = llvmDataLayout ?lc
   let endianness = dl^.intLayout
   mem0 <- emptyMem endianness

   -- allocate pointers values for function symbols, but do not
   -- yet bind them to function handles
   let decls = allModuleDeclares m
   mem <- foldM (allocLLVMFunPtr sym llvm_ctx) mem0 decls

   -- Allocate global values
   let globAliases = llvmGlobalAliases llvm_ctx
   let globals     = L.modGlobals m
   gs_alloc <- mapM (\g -> do
                        let err msg = malformedLLVMModule
                                    ("Invalid type for global" <> fromString (show (L.globalSym g)))
                                    [fromString msg]
                        ty <- either err return $ liftMemType $ L.globalType g
                        let sz      = memTypeSize dl ty
                        let tyAlign = memTypeAlign dl ty
                        let aliases = map L.aliasName . Set.toList $
                              fromMaybe Set.empty (Map.lookup (L.globalSym g) globAliases)
                        -- LLVM documentation regarding global variable alignment:
                        --
                        -- An explicit alignment may be specified for
                        -- a global, which must be a power of 2. If
                        -- not present, or if the alignment is set to
                        -- zero, the alignment of the global is set by
                        -- the target to whatever it feels
                        -- convenient. If an explicit alignment is
                        -- specified, the global is forced to have
                        -- exactly that alignment.
                        alignment <-
                          case L.globalAlign g of
                            Just a | a > 0 ->
                              case toAlignment (toBytes a) of
                                Nothing -> fail $ "Invalid alignemnt: " ++ show a ++ "\n  " ++
                                                  "specified for global: " ++ show (L.globalSym g)
                                Just al -> return al
                            _ -> return tyAlign
                        return (g, aliases, sz, alignment))
                    globals
   allocGlobals sym (filter (\(g, _, _, _) -> predicate g) gs_alloc) mem


allocLLVMFunPtr ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  sym ->
  LLVMContext arch ->
  MemImpl sym ->
  L.Declare ->
  IO (MemImpl sym)
allocLLVMFunPtr sym llvm_ctx mem decl =
  do let symbol@(L.Symbol sym_str) = L.decName decl
     let funAliases = llvmFunctionAliases llvm_ctx
     let aliases = map L.aliasName $ maybe [] Set.toList $ Map.lookup symbol funAliases
     z <- bvLit sym ?ptrWidth (BV.zero ?ptrWidth)
     (ptr, mem') <- doMalloc sym G.GlobalAlloc G.Immutable sym_str mem z noAlignment
     return $ registerGlobal mem' (symbol:aliases) ptr

------------------------------------------------------------------------
-- ** populateGlobals

-- | Populate the globals mentioned in the given @GlobalInitializerMap@
--   provided they satisfy the given filter function.
--
--   This will (necessarily) populate any globals that the ones in the
--   filtered list transitively reference.
populateGlobals ::
  ( ?lc :: TypeContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , HasLLVMAnn sym
  , IsSymInterface sym ) =>
  (L.Global -> Bool)   {- ^ Filter function, globals that cause this to return true will be populated -} ->
  sym ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateGlobals select sym gimap mem0 = foldM f mem0 (Map.elems gimap)
  where
  f mem (gl, _) | not (select gl)    = return mem
  f _   (_,  Left msg)               = fail msg
  f mem (gl, Right (mty, Just cval)) = populateGlobal sym gl mty cval gimap mem
  f mem (_ , Right (_, Nothing))     = return mem


-- | Populate all the globals mentioned in the given @GlobalInitializerMap@.
populateAllGlobals ::
  ( ?lc :: TypeContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , HasLLVMAnn sym
  , IsSymInterface sym ) =>
  sym ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateAllGlobals = populateGlobals (const True)


-- | Populate only the constant global variables mentioned in the
--   given @GlobalInitializerMap@ (and any they transitively refer to).
populateConstGlobals ::
  ( ?lc :: TypeContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , HasLLVMAnn sym
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
populateGlobal :: forall sym wptr.
  ( ?lc :: TypeContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymInterface sym
  , HasLLVMAnn sym
  , HasCallStack
  ) =>
  sym ->
  L.Global {- ^ The global to populate -} ->
  MemType {- ^ Type of the global -} ->
  LLVMConst {- ^ Constant value to initialize with -} ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateGlobal sym gl memty cval giMap mem =
  do let alignment = memTypeAlign (llvmDataLayout ?lc) memty

     -- So that globals can populate and look up the globals they reference
     -- during initialization
     let populateRec :: HasCallStack
                     => L.Symbol -> StateT (MemImpl sym) IO (LLVMPtr sym wptr)
         populateRec symbol = do
           memimpl0 <- get
           memimpl <-
            case Map.lookup symbol (memImplGlobalMap mem) of
              Just _  -> pure memimpl0 -- We already populated this one
              Nothing ->
                -- For explanations of the various modes of failure, see the
                -- comment on 'GlobalInitializerMap'.
                case Map.lookup symbol giMap of
                  Nothing -> fail $ unlines $
                    [ "Couldn't find global variable: " ++ show symbol ]
                  Just (glob, Left str) -> fail $ unlines $
                    [ "Couldn't find global variable's initializer: " ++
                        show symbol
                    , "Reason:"
                    , str
                    , "Full definition:"
                    , show glob
                    ]
                  Just (glob, Right (_, Nothing)) -> fail $ unlines $
                    [ "Global was not a compile-time constant:" ++ show symbol
                    , "Full definition:"
                    , show glob
                    ]
                  Just (glob, Right (memty_, Just cval_)) ->
                    liftIO $ populateGlobal sym glob memty_ cval_ giMap mem
           put memimpl
           liftIO $ doResolveGlobal sym memimpl symbol

     ty <- toStorableType memty
     ptr <- doResolveGlobal sym mem (L.globalSym gl)
     (val, mem') <- runStateT (constToLLVMValP sym populateRec cval) mem
     storeConstRaw sym mem' ptr ty alignment val
