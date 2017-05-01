-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics
-- Description      : Override definitions for LLVM intrisic and basic
--                    library functions
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.LLVM.Intrinsics
( llvmIntrinsicTypes
, llvmIntrinsics
, LLVMHandleInfo(..)
, LLVMContext(..)
, LLVMOverride
, SymbolHandleMap
, symbolMap
, mkLLVMContext
, register_llvm_override
, register_llvm_overrides
) where

import qualified Codec.Binary.UTF8.Generic as UTF8
import           Control.Lens hiding (op)
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Vector as V
import           System.IO
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName ( functionNameFromText )
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Solver.Interface

import           Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Common as G
import           Lang.Crucible.LLVM.Printf
import           Lang.Crucible.Utils.MonadST


llvmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmIntrinsicTypes =
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_memory") IntrinsicMuxFn $
   MapF.empty


llvmIntrinsics :: HandleAllocator s
               -> DataLayout
               -> ST s (LLVMMemOps, AnyFnBindings)
llvmIntrinsics halloc dl = do
  memOps <- newMemOps halloc dl
  let fns = AnyFnBindings (llvmMemIntrinsics memOps)
  return (memOps, fns)


register_llvm_overrides :: IsSymInterface sym
                        => StateT LLVMContext (OverrideSim p sym rtp l a) ()
register_llvm_overrides = do
  -- Register translation intrinsics
  AnyFnBindings fns <- llvmFnBindings <$> get
  lift $ mapM_ registerFnBinding fns

  -- LLVM Compiler intrinsics
  register_llvm_override llvmLifetimeStartOverride
  register_llvm_override llvmLifetimeEndOverride
  register_llvm_override llvmMemcpyOverride_8_8_32
  register_llvm_override llvmMemcpyOverride_8_8_64
  register_llvm_override llvmMemmoveOverride_8_8_32
  register_llvm_override llvmMemmoveOverride_8_8_64
  register_llvm_override llvmMemsetOverride_8_32
  register_llvm_override llvmMemsetOverride_8_64
  register_llvm_override llvmObjectsizeOverride_32
  register_llvm_override llvmObjectsizeOverride_64

  -- C standard libraray functions
  register_llvm_override llvmMemcpyOverride
  register_llvm_override llvmMemmoveOverride
  register_llvm_override llvmMemsetOverride
  register_llvm_override llvmMallocOverride
  register_llvm_override llvmCallocOverride
  register_llvm_override llvmFreeOverride

  register_llvm_override llvmPrintfOverride
  register_llvm_override llvmPutsOverride

------------------------------------------------------------------------
-- LLVMHandleInfo

-- | Information about an LLVM handle, including both its
--   LLVM and Crucible type information as well as the Crucible
--   handle allocated to this symbol.
data LLVMHandleInfo where
  LLVMHandleInfo :: L.Declare
                 -> FnHandle init ret
                 -> LLVMHandleInfo

------------------------------------------------------------------------
-- LLVMContext

-- | Maps symbol to information about associated handle.
type SymbolHandleMap = Map L.Symbol LLVMHandleInfo

-- | Information about the LLVM module.
data LLVMContext
   = LLVMContext
   { -- | Map LLVM symbols to their associated state.
     _symbolMap  :: !SymbolHandleMap
   , memModelOps :: !LLVMMemOps
   , llvmTypeCtx :: TyCtx.LLVMContext
   , llvmFnBindings :: AnyFnBindings
   }

symbolMap :: Simple Lens LLVMContext SymbolHandleMap
symbolMap = lens _symbolMap (\s v -> s { _symbolMap = v })

mkLLVMContext :: HandleAllocator s
              -> L.Module
              -> ST s LLVMContext
mkLLVMContext halloc m = do
  let (errs, typeCtx) = TyCtx.llvmContextFromModule m
  unless (null errs) $
          fail $ unlines $ [ "Failed to construct LLVM type context:" ]
                           ++
                           map show errs
  let dl = TyCtx.llvmDataLayout typeCtx
  (memOps, fns) <- llvmIntrinsics halloc dl
  let ctx = LLVMContext
            { _symbolMap = Map.empty
            , memModelOps = memOps
            , llvmTypeCtx = typeCtx
            , llvmFnBindings = fns
            }
  return ctx

type LLVMOverride p sym args ret = (L.Declare, LLVMMemOps -> Override p sym args ret)

register_llvm_override :: forall p args ret sym l a rtp
                       . (KnownCtx TypeRepr args, KnownRepr TypeRepr ret)
                      => LLVMOverride p sym args ret
                      -> StateT LLVMContext (OverrideSim p sym rtp l a) ()
register_llvm_override (decl,o_f) = do
  llvmctx <- get
  let o = o_f (memModelOps llvmctx)
  let fnm = overrideName o
  let nm  = L.decName decl
  case Map.lookup nm (llvmctx^.symbolMap) of
    Just (LLVMHandleInfo _decl' h) -> do
      let argTypes = handleArgTypes h
      let retType  = handleReturnType h
      case testEquality argTypes (knownRepr :: CtxRepr args) of
        Nothing ->
          fail $ unwords ["argument type mismatch when registering LLVM mss override", show nm]
        Just Refl ->
          case testEquality retType (knownRepr :: TypeRepr ret) of
            Nothing ->
              fail $ unwords ["return type mismatch when registering LLVM mss override", show nm]
            Just Refl -> lift $ bindFnHandle h (UseOverride o)

    Nothing -> do
      ctx <- lift $ use stateContext
      let ha = simHandleAllocator ctx
      h <- lift $ liftST $ mkHandle ha fnm
      lift $ bindFnHandle h (UseOverride o)
      put (llvmctx & symbolMap %~ Map.insert nm (LLVMHandleInfo decl h))


llvmLifetimeStartOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> BVType 64 ::> LLVMPointerType) UnitType
llvmLifetimeStartOverride =
  let nm = "llvm.lifetime.start" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 64, L.PtrTo (L.PrimType $ L.Integer 8) ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \_ -> mkOverride (functionNameFromText (Text.pack nm)) (return ())
  )

llvmLifetimeEndOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> BVType 64 ::> LLVMPointerType) UnitType
llvmLifetimeEndOverride =
  let nm = "llvm.lifetime.end" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 64, L.PtrTo (L.PrimType $ L.Integer 8) ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \_ -> mkOverride (functionNameFromText (Text.pack nm)) (return ())
  )

llvmObjectsizeOverride_32
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32 =
  let nm = "llvm.objectsize.i32.p0i8" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args
  )

llvmObjectsizeOverride_64
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64 =
  let nm = "llvm.objectsize.i64.p0i8" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 64
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args
  )


llvmCallocOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> BVType PtrWidth ::> BVType PtrWidth)
                      LLVMPointerType
llvmCallocOverride =
  let nm = "calloc" in
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     , L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callCalloc sym memOps) args
  )


llvmMallocOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> BVType PtrWidth)
                      LLVMPointerType
llvmMallocOverride =
  let nm = "malloc" in
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMalloc sym memOps) args
  )

llvmFreeOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType)
                      UnitType
llvmFreeOverride =
  let nm = "free" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Void
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callFree sym memOps) args
  )


llvmMemcpyOverride_8_8_32
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType
                                ::> BVType 32 ::> BVType 32 ::> BVType 1)
                      UnitType
llvmMemcpyOverride_8_8_32 =
  let nm = "llvm.memcpy.p0i8.p0i8.i32" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMemcpy sym memOps) args
  )


llvmMemcpyOverride_8_8_64
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType
                                ::> BVType 64 ::> BVType 32 ::> BVType 1)
                      UnitType
llvmMemcpyOverride_8_8_64 =
  let nm = "llvm.memcpy.p0i8.p0i8.i64" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 64
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMemcpy sym memOps) args
  )

llvmMemcpyOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType
                                ::> LLVMPointerType
                                ::> BVType PtrWidth)
                      LLVMPointerType
llvmMemcpyOverride =
  let nm = "memcpy" in
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType L.Void
                     , L.PtrTo $ L.PrimType L.Void
                     , L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       align    <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat 0
       volatile <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat 0
       Ctx.uncurryAssignment (callMemcpy sym memOps)
                             (args Ctx.%> align Ctx.%> volatile)
       return $ regValue $ args^._1 -- return first argument
  )

llvmMemmoveOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType
                                ::> LLVMPointerType
                                ::> BVType PtrWidth)
                      LLVMPointerType
llvmMemmoveOverride =
  let nm = "memmove" in
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType L.Void
                     , L.PtrTo $ L.PrimType L.Void
                     , L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       align <- liftIO (RegEntry knownRepr <$> bvLit sym knownNat 0)
       volatile <- liftIO (RegEntry knownRepr <$> bvLit sym knownNat 0)
       Ctx.uncurryAssignment (callMemmove sym memOps)
                             (args Ctx.%> align Ctx.%> volatile)
       return $ regValue $ args^._1 -- return first argument
  )


llvmMemmoveOverride_8_8_32
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType
                                ::> BVType 32 ::> BVType 32 ::> BVType 1)
                      UnitType
llvmMemmoveOverride_8_8_32 =
  let nm = "llvm.memmove.p0i8.p0i8.i32" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMemmove sym memOps) args
  )

llvmMemmoveOverride_8_8_64
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType
                                ::> BVType 64 ::> BVType 32 ::> BVType 1)
                      UnitType
llvmMemmoveOverride_8_8_64 =
  let nm = "llvm.memmove.p0i8.p0i8.i64" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 64
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMemmove sym memOps) args
  )

llvmMemsetOverride_8_64
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType
                                ::> BVType  8
                                ::> BVType 64
                                ::> BVType 32
                                ::> BVType 1)
                      UnitType
llvmMemsetOverride_8_64 =
  let nm = "llvm.memset.p0i8.i64" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer  8
                     , L.PrimType $ L.Integer 64
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer  1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMemset sym memOps) args
  )

llvmMemsetOverride_8_32
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType
                                ::> BVType  8
                                ::> BVType 32
                                ::> BVType 32
                                ::> BVType 1)
                      UnitType
llvmMemsetOverride_8_32 =
  let nm = "llvm.memset.p0i8.i32" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer  8
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer  1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callMemset sym memOps) args
  )


llvmMemsetOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType
                                ::> BVType PtrWidth
                                ::> BVType PtrWidth)
                      LLVMPointerType
llvmMemsetOverride =
  let nm = "memset" in
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Void
                     , L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     , L.PrimType $ L.Integer (fromIntegral $ natValue ptrWidth)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       let dest = args^._1
       val <- liftIO
            (RegEntry knownRepr <$> bvTrunc sym knownNat (regValue (args^._2)))
       let len = args^._3
       align <- liftIO
          (RegEntry knownRepr <$> bvLit sym knownNat 0)
       volatile <- liftIO
          (RegEntry knownRepr <$> bvLit sym knownNat 0)
       callMemset sym memOps dest val len align volatile
       return (regValue dest)
  )


llvmPutsOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType) (BVType 32)
llvmPutsOverride =
  let nm = "puts" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callPuts sym memOps) args
  )


llvmPrintfOverride
  :: IsSymInterface sym
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType
                                ::> VectorType AnyType)
                      (BVType 32)
llvmPrintfOverride =
  let nm = "printf" in
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = True
    , L.decAttrs   = []
    }
  , \memOps -> mkOverride (functionNameFromText (Text.pack nm)) $ do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (callPrintf sym memOps) args
  )

callMalloc
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym (BVType PtrWidth)
  -> OverrideSim p sym r args ret (RegValue sym LLVMPointerType)
callMalloc sym memOps
           (regValue -> sz) = do
  --liftIO $ putStrLn "MEM MALLOC"
  mem <- readGlobal (llvmMemVar memOps)
  (p, mem') <- liftIO $ doMalloc sym mem sz
  writeGlobal (llvmMemVar memOps) mem'
  return p


callCalloc
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym (BVType PtrWidth)
  -> RegEntry sym (BVType PtrWidth)
  -> OverrideSim p sym r args ret (RegValue sym LLVMPointerType)
callCalloc sym memOps
           (regValue -> sz)
           (regValue -> num) = do
  --liftIO $ putStrLn "MEM CALLOC"
  mem <- readGlobal (llvmMemVar memOps)
  (p, mem') <- liftIO $ doCalloc sym mem sz num
  writeGlobal (llvmMemVar memOps) mem'
  return p


callFree
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym LLVMPointerType
  -> OverrideSim p sym r args ret ()
callFree sym memOps
           (regValue -> ptr) = do
  --liftIO $ putStrLn "MEM FREE"
  mem <- readGlobal (llvmMemVar memOps)
  mem' <- liftIO $ doFree sym mem ptr
  writeGlobal (llvmMemVar memOps) mem'


callMemcpy
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym r args ret ()
callMemcpy sym memOps
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _align _volatile = do
  -- FIXME? add assertions about alignment
  --liftIO $ putStrLn "MEM COPY"
  mem <- readGlobal (llvmMemVar memOps)
  liftIO $ assertDisjointRegions sym w dest src len
  mem' <- liftIO $ doMemcpy sym w mem dest src len
  writeGlobal (llvmMemVar memOps) mem'

-- NB the only difference between memcpy and memove
-- is that memmove does not assert that the memory
-- ranges are disjoint.  The underlying operation
-- works correctly in both cases.
callMemmove
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym r args ret ()
callMemmove sym memOps
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _align _volatile = do
  -- FIXME? add assertions about alignment
  --liftIO $ putStrLn "MEM MOVE"
  mem <- readGlobal (llvmMemVar memOps)
  mem' <- liftIO $ doMemcpy sym w mem dest src len
  writeGlobal (llvmMemVar memOps) mem'

callMemset
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym (BVType 8)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym r args ret ()
callMemset sym memOps
           (regValue -> dest)
           (regValue -> val)
           (RegEntry (BVRepr w) len)
           _align _volatile = do
  -- FIXME? add assertions about alignment
  --liftIO $ putStrLn "MEM SET"
  mem <- readGlobal (llvmMemVar memOps)
  mem' <- liftIO $ doMemset sym w mem dest val len
  writeGlobal (llvmMemVar memOps) mem'

-- Excerpt from the LLVM documentation:
--
-- The llvm.objectsize intrinsic is designed to provide information to
-- the optimizers to determine at compile time whether a) an operation
-- (like memcpy) will overflow a buffer that corresponds to an object,
-- or b) that a runtime check for overflow isn’t necessary. An object
-- in this context means an allocation of a specific class, structure,
-- array, or other object.
--
-- The llvm.objectsize intrinsic takes two arguments. The first
-- argument is a pointer to or into the object. The second argument is
-- a boolean and determines whether llvm.objectsize returns 0 (if
-- true) or -1 (if false) when the object size is unknown. The second
-- argument only accepts constants.
--
-- The llvm.objectsize intrinsic is lowered to a constant representing
-- the size of the object concerned. If the size cannot be determined
-- at compile time, llvm.objectsize returns i32/i64 -1 or 0 (depending
-- on the min argument).
callObjectsize
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> LLVMMemOps
  -> NatRepr w
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym r args ret (RegValue sym (BVType w))
callObjectsize sym _memOps w
  (regValue -> _ptr)
  (regValue -> flag) = liftIO $ do
    -- Ignore the pointer value, and just return the value for unknown, as
    -- defined by the documenatation.  If an `objectsize` invocation survives
    -- through compilation for us to see, that means the compiler could not
    -- determine the value.
    t <- bvIsNonzero sym flag
    z <- bvLit sym w 0
    n <- bvNotBits sym z -- NB: -1 is the boolean negation of zero
    bvIte sym t z n


callPuts
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym LLVMPointerType
  -> OverrideSim p sym r args ret (RegValue sym (BVType 32))
callPuts sym memOps
  (regValue -> strPtr) = do
    mem <- readGlobal (llvmMemVar memOps)
    str <- liftIO $ loadString sym mem strPtr Nothing
    h <- printHandle <$> getContext
    liftIO $ hPutStrLn h (UTF8.toString str)
    -- return non-negative value on success
    liftIO $ bvLit sym knownNat 1


callPrintf
  :: IsSymInterface sym
  => sym
  -> LLVMMemOps
  -> RegEntry sym LLVMPointerType
  -> RegEntry sym (VectorType AnyType)
  -> OverrideSim p sym r args ret (RegValue sym (BVType 32))
callPrintf sym memOps
  (regValue -> strPtr)
  (regValue -> valist) = do
    mem <- readGlobal (llvmMemVar memOps)
    formatStr <- liftIO $ loadString sym mem strPtr Nothing
    case parseDirectives formatStr of
      Left err -> fail err
      Right ds -> do
        ((str, n), mem') <- liftIO $ runStateT (executeDirectives (printfOps sym valist) ds) mem
        writeGlobal (llvmMemVar memOps) mem'
        h <- printHandle <$> getContext
        liftIO $ hPutStr h str
        liftIO $ bvLit sym knownNat (toInteger n)

printfOps :: IsSymInterface sym
          => sym
          -> V.Vector (AnyValue sym)
          -> PrintfOperations (StateT (MemImpl sym PtrWidth) IO)
printfOps sym valist =
  PrintfOperations
  { printfGetInteger = \i sgn _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (BVRepr _w) x) ->
         if sgn then
           return $ asSignedBV x
         else
           return $ asUnsignedBV x
       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected integer, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetFloat = \i _len ->
     case valist V.!? (i-1) of
       Just (AnyValue RealValRepr x) ->
         return $ asRational x
       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected floating-point, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetString  = \i numchars ->
     case valist V.!? (i-1) of
       Just (AnyValue (RecursiveRepr nm) ptr)
         | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") -> do
              mem <- get
              liftIO $ loadString sym mem ptr numchars
       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected char*, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetPointer = \i ->
     case valist V.!? (i-1) of
       Just (AnyValue (RecursiveRepr nm) ptr)
         | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") -> do
             return $ show (ppPtr ptr)
       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected void*, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfSetInteger = \i len v ->
     case valist V.!? (i-1) of
       Just (AnyValue (RecursiveRepr nm) ptr)
         | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") -> do
            mem <- get
            case len of
              Len_Byte  -> do
                 let w  = knownNat :: NatRepr 8
                 let tp = G.bitvectorType 1
                 x <- AnyValue (BVRepr w) <$> (liftIO $ bvLit sym w $ toInteger v)
                 mem' <- liftIO $ doStore sym mem ptr tp x
                 put mem'
              Len_Short -> do
                 let w  = knownNat :: NatRepr 16
                 let tp = G.bitvectorType 2
                 x <- AnyValue (BVRepr w) <$> (liftIO $ bvLit sym w $ toInteger v)
                 mem' <- liftIO $ doStore sym mem ptr tp x
                 put mem'
              Len_NoMod -> do
                 let w  = knownNat :: NatRepr 32
                 let tp = G.bitvectorType 4
                 x <- AnyValue (BVRepr w) <$> (liftIO $ bvLit sym w $ toInteger v)
                 mem' <- liftIO $ doStore sym mem ptr tp x
                 put mem'
              Len_Long  -> do
                 let w  = knownNat :: NatRepr 64
                 let tp = G.bitvectorType 8
                 x <- AnyValue (BVRepr w) <$> (liftIO $ bvLit sym w $ toInteger v)
                 mem' <- liftIO $ doStore sym mem ptr tp x
                 put mem'
              _ ->
                fail $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected void*, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]
  }
