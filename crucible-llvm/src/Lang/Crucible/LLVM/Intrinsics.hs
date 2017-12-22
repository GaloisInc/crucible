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
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.LLVM.Intrinsics
( llvmIntrinsicTypes
, llvmIntrinsics
, LLVMHandleInfo(..)
, LLVMContext(..)
, LLVMOverride(..)
, SymbolHandleMap
, symbolMap
, llvmTypeCtx
, mkLLVMContext
, register_llvm_override
, register_llvm_overrides
, build_llvm_override
, llvmDeclToFunHandleRepr
) where

import qualified Codec.Binary.UTF8.Generic as UTF8
import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Vector as V
import           System.IO
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface

import           Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.Pointer
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.Printf
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.Utils.MonadST


llvmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmIntrinsicTypes =
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_memory") IntrinsicMuxFn $
   MapF.empty

llvmIntrinsics :: HasPtrWidth wptr
               => HandleAllocator s
               -> DataLayout
               -> ST s (LLVMMemOps wptr, AnyFnBindings LLVM)
llvmIntrinsics halloc dl = do
  memOps <- newMemOps halloc dl
  let fns = AnyFnBindings (llvmMemIntrinsics memOps)
  return (memOps, fns)


register_llvm_overrides :: (IsSymInterface sym, HasPtrWidth wptr)
                        => StateT (LLVMContext wptr) (OverrideSim p sym LLVM rtp l a) ()
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

  -- FIXME, all variants of llvm.ctlz....
  register_llvm_override llvmCtlz32

  -- FIXME, all variants of llvm.cttz, llvm.bitreverse, llvm.bswap, llvm.ctpop,
  -- llvm.sadd.with.overflow, llvm.uadd.with.overflow, llvm.ssub.with.overflow,
  -- llvm.usub.with.overflow, llvm.smul.with.overflow, llvm.umul.with.overflow,

  -- C standard library functions
  register_llvm_override llvmAssertRtnOverride

  register_llvm_override llvmMemcpyOverride
  register_llvm_override llvmMemcpyChkOverride
  register_llvm_override llvmMemmoveOverride
  register_llvm_override llvmMemsetOverride
  register_llvm_override llvmMemsetChkOverride
  register_llvm_override llvmMallocOverride
  register_llvm_override llvmCallocOverride
  register_llvm_override llvmFreeOverride

  register_llvm_override llvmPrintfOverride
  register_llvm_override llvmPutsOverride
  register_llvm_override llvmPutCharOverride

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
data LLVMContext wptr
   = LLVMContext
   { -- | Map LLVM symbols to their associated state.
     _symbolMap     :: !SymbolHandleMap
   , llvmPtrWidth   :: forall a. (16 <= wptr => NatRepr wptr -> a) -> a
   , memModelOps    :: !(LLVMMemOps wptr)
   , _llvmTypeCtx    :: TyCtx.LLVMContext
   , llvmFnBindings :: AnyFnBindings LLVM
   }

symbolMap :: Simple Lens (LLVMContext wptr) SymbolHandleMap
symbolMap = lens _symbolMap (\s v -> s { _symbolMap = v })

llvmTypeCtx :: Simple Lens (LLVMContext wptr) TyCtx.LLVMContext
llvmTypeCtx = lens _llvmTypeCtx (\s v -> s{ _llvmTypeCtx = v })

mkLLVMContext :: HandleAllocator s
              -> L.Module
              -> ST s (Some LLVMContext)
mkLLVMContext halloc m = do
  let (errs, typeCtx) = TyCtx.llvmContextFromModule m
  unless (null errs) $
          fail $ unlines $ [ "Failed to construct LLVM type context:" ]
                           ++
                           map show errs
  let dl = TyCtx.llvmDataLayout typeCtx
  case someNat (toInteger (ptrBitwidth dl)) of
    Just (Some (wptr :: NatRepr wptr)) | Just LeqProof <- testLeq (knownNat @16) wptr ->
      withPtrWidth wptr $
        do (memOps, fns) <- llvmIntrinsics halloc dl
           let ctx = LLVMContext
                     { _symbolMap = Map.empty
                     , memModelOps = memOps
                     , llvmPtrWidth = \x -> x wptr
                     , _llvmTypeCtx = typeCtx
                     , llvmFnBindings = fns
                     }
           return (Some ctx)
    _ ->
      fail ("Cannot load LLVM bitcode file with illegal pointer width: " ++ show (dl^.ptrSize))


data LLVMOverride p sym wptr args ret =
  LLVMOverride
  { llvmOverride_declare :: L.Declare
  , llvmOverride_args :: CtxRepr args
  , llvmOverride_ret  :: TypeRepr ret
  , llvmOverride_def ::
       forall rtp args' ret'.
         LLVMMemOps wptr ->
         sym ->
         Ctx.Assignment (RegEntry sym) args ->
         OverrideSim p sym LLVM rtp args' ret' (RegValue sym ret)
  }


newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym LLVM rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall rtp l a.
    RegValue sym tp ->
    OverrideSim p sym LLVM rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall m p sym args args'.
  (IsSymInterface sym, Monad m) =>
  sym ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym args args')
transformLLVMArgs sym args' args =
  case (Ctx.view args', Ctx.view args) of
    (Ctx.AssignEmpty, Ctx.AssignEmpty) ->
      return (ArgTransformer (\_ -> return Ctx.Empty))
    (Ctx.AssignExtend rest' tp', Ctx.AssignExtend rest tp) ->
      do return (ArgTransformer
           (\z -> case Ctx.view z of
                    Ctx.AssignExtend xs x ->
                      do (ValTransformer f)  <- transformLLVMRet sym tp tp'
                         (ArgTransformer fs) <- transformLLVMArgs sym rest' rest
                         xs' <- fs xs
                         x'  <- RegEntry tp' <$> f (regValue x)
                         return (xs' :> x')))
    _ -> fail "transformLLVMArgs: argument shape mismatch!"

transformLLVMRet ::
  (IsSymInterface sym, Monad m) =>
  sym ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ret ret')
transformLLVMRet sym (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . llvmPointer_bv sym))
transformLLVMRet sym (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . projectLLVM_bv sym))
transformLLVMRet _sym ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformLLVMRet _sym ret ret'
  = fail $ unwords ["Cannot transform", show ret, "value into", show ret']

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the LLVM calling convention.  This basically just coerces
--   between values of @BVType w@ and values of @LLVMPointerType w@.
build_llvm_override ::
  IsSymInterface sym =>
  sym ->
  FunctionName ->
  CtxRepr args  ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall rtp' l' a'. Ctx.Assignment (RegEntry sym) args ->
   OverrideSim p sym LLVM rtp' l' a' (RegValue sym ret)) ->
  OverrideSim p sym LLVM rtp l a (Override p sym LLVM args' ret')
build_llvm_override sym fnm args ret args' ret' llvmOverride =
  do fargs <- transformLLVMArgs sym args args'
     fret  <- transformLLVMRet  sym ret  ret'
     return $ mkOverride' fnm ret' $
            do RegMap xs <- getOverrideArgs
               applyValTransformer fret =<< llvmOverride =<< applyArgTransformer fargs xs

register_llvm_override :: forall p args ret sym wptr l a rtp
                       . (IsSymInterface sym, HasPtrWidth wptr)
                      => LLVMOverride p sym wptr args ret
                      -> StateT (LLVMContext wptr) (OverrideSim p sym LLVM rtp l a) ()
register_llvm_override llvmOverride = do
  llvmctx <- get
  let decl = llvmOverride_declare llvmOverride
  let nm@(L.Symbol str_nm) = L.decName decl
  let fnm  = functionNameFromText (Text.pack str_nm)

  sym <- lift $ getSymInterface

  let memOps = memModelOps llvmctx
  let overrideArgs = llvmOverride_args llvmOverride
  let overrideRet  = llvmOverride_ret llvmOverride

  let ?lc = llvmctx^.llvmTypeCtx

  decl' <- liftDeclare decl
  llvmDeclToFunHandleRepr decl' $ \derivedArgs derivedRet -> do
    o <- lift $ build_llvm_override sym fnm overrideArgs overrideRet derivedArgs derivedRet
                  (llvmOverride_def llvmOverride memOps sym)
    case Map.lookup nm (llvmctx^.symbolMap) of
      Just (LLVMHandleInfo _decl' h) -> do
        case testEquality (handleArgTypes h) derivedArgs of
           Nothing ->
             fail $ unwords ["argument type mismatch when registering LLVM mss override", show nm]
           Just Refl ->
             case testEquality (handleReturnType h) derivedRet of
               Nothing ->
                 fail $ unwords ["return type mismatch when registering LLVM mss override", show nm]
               Just Refl -> lift $ bindFnHandle h (UseOverride o)
      Nothing ->
        do ctx <- lift $ use stateContext
           let ha = simHandleAllocator ctx
           h <- lift $ liftST $ mkHandle' ha fnm derivedArgs derivedRet
           lift $ bindFnHandle h (UseOverride o)
           put (llvmctx & symbolMap %~ Map.insert nm (LLVMHandleInfo decl h))


-- | Convenient LLVM representation of the @size_t@ type.
llvmSizeT :: HasPtrWidth wptr => L.Type
llvmSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

llvmLifetimeStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeStartOverride =
  let nm = "llvm.lifetime.start" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 64, L.PtrTo (L.PrimType $ L.Integer 8) ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> KnownBV @64 :> PtrRepr)
  UnitRepr
  (\_ops _sym _args -> return ())

llvmLifetimeEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeEndOverride =
  let nm = "llvm.lifetime.end" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 64, L.PtrTo (L.PrimType $ L.Integer 8) ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> KnownBV @64 :> PtrRepr)
  UnitRepr
  (\_ops _sym _args -> return ())


llvmObjectsizeOverride_32
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32 =
  let nm = "llvm.objectsize.i32.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args)

llvmObjectsizeOverride_64
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64 =
  let nm = "llvm.objectsize.i64.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 64
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1)
  (KnownBV @64)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args)

llvmAssertRtnOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
        UnitType
llvmAssertRtnOverride =
  let nm = "__assert_rtn" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 32
                     , L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @32 :> PtrRepr)
  UnitRepr
  (\_ sym _args ->
       do let err = AssertFailureSimError "Call to __assert_rtn"
          liftIO $ addAssertion sym (falsePred sym) err
  )

llvmCallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> BVType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmCallocOverride =
  let nm = "calloc" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ llvmSizeT
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> SizeT :> SizeT)
  (PtrRepr)
  (\memOps sym args -> Ctx.uncurryAssignment (callCalloc sym memOps) args)

llvmMallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMallocOverride =
  let nm = "malloc" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> SizeT)
  (PtrRepr)
  (\memOps sym args -> Ctx.uncurryAssignment (callMalloc sym memOps) args)

llvmFreeOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr)
         UnitType
llvmFreeOverride =
  let nm = "free" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Void
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callFree sym memOps) args)

llvmMemcpyOverride_8_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32 =
  let nm = "llvm.memcpy.p0i8.p0i8.i32" in
  LLVMOverride
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
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @32 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callMemcpy sym memOps) args)


llvmMemcpyOverride_8_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64 =
  let nm = "llvm.memcpy.p0i8.p0i8.i64" in
  LLVMOverride
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
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @64 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callMemcpy sym memOps) args)

llvmMemcpyOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (LLVMPointerType wptr)
llvmMemcpyOverride =
  let nm = "memcpy" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType L.Void
                     , L.PtrTo $ L.PrimType L.Void
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> SizeT)
  PtrRepr
  (\memOps sym args ->
     do align    <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat 0
        volatile <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat 0
        Ctx.uncurryAssignment (callMemcpy sym memOps)
                              (args :> align :> volatile)
        return $ regValue $ args^._1 -- return first argument
  )


llvmMemcpyChkOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> LLVMPointerType wptr
                   ::> BVType wptr
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemcpyChkOverride =
  let nm = "__memcpy_chk" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType L.Void
                     , L.PtrTo $ L.PrimType L.Void
                     , llvmSizeT
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> SizeT :> SizeT)
  PtrRepr
  (\memOps sym args ->
    do let args' = Ctx.empty :> (args^._1) :> (args^._2) :> (args^._3)
       align    <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat 0
       volatile <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat 0
       Ctx.uncurryAssignment (callMemcpy sym memOps)
                             (args' :> align :> volatile)
       return $ regValue $ args^._1 -- return first argument
  )

llvmMemmoveOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> (LLVMPointerType wptr)
                   ::> (LLVMPointerType wptr)
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemmoveOverride =
  let nm = "memmove" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType L.Void
                     , L.PtrTo $ L.PrimType L.Void
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> SizeT)
  PtrRepr
  (\memOps sym args ->
    do align <- liftIO (RegEntry knownRepr <$> bvLit sym knownNat 0)
       volatile <- liftIO (RegEntry knownRepr <$> bvLit sym knownNat 0)
       Ctx.uncurryAssignment (callMemmove sym memOps)
                             (args :> align :> volatile)
       return $ regValue $ args^._1 -- return first argument
  )

llvmMemmoveOverride_8_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32 =
  let nm = "llvm.memmove.p0i8.p0i8.i32" in
  LLVMOverride
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
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @32 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callMemmove sym memOps) args)


llvmMemmoveOverride_8_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64 =
  let nm = "llvm.memmove.p0i8.p0i8.i64" in
  LLVMOverride
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
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @64 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callMemmove sym memOps) args)


llvmCtlz32
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> BVType 32 ::> BVType 1)
         (BVType 32)
llvmCtlz32 =
  let nm = "llvm.ctlz.i32" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> KnownBV @32 :> KnownBV @1)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callCtlz sym memOps) args)

llvmMemsetOverride_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64 =
  let nm = "llvm.memset.p0i8.i64" in
  LLVMOverride
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
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @8 :> KnownBV @64 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callMemset sym memOps) args)


llvmMemsetOverride_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32 =
  let nm = "llvm.memset.p0i8.i32" in
  LLVMOverride
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
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @8 :> KnownBV @32 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callMemset sym memOps) args)


llvmMemsetOverride :: forall p sym wptr.
     (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr
                 ::> BVType wptr
                 ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetOverride =
  let nm = "memset" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Void
                     , llvmSizeT
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> SizeT :> SizeT)
  PtrRepr
  (\memOps sym args ->
    do LeqProof <- return (leqTrans @9 @16 @wptr LeqProof LeqProof)
       let dest = args^._1
       val <- liftIO (RegEntry knownRepr <$> bvTrunc sym (knownNat @8) (regValue (args^._2)))
       let len = args^._3
       align <- liftIO
          (RegEntry knownRepr <$> bvLit sym knownNat 0)
       volatile <- liftIO
          (RegEntry knownRepr <$> bvLit sym knownNat 0)
       callMemset sym memOps dest val len align volatile
       return (regValue dest)
  )

llvmMemsetChkOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr
                 ::> BVType 32
                 ::> BVType wptr
                 ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetChkOverride =
  let nm = "__memset_chk" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType L.Void
                     , L.PrimType $ L.Integer 32
                     , llvmSizeT
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @32 :> SizeT :> SizeT)
  PtrRepr
  (\memOps sym args ->
    do let dest = args^._1
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

llvmPutCharOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr (EmptyCtx ::> BVType 32) (BVType 32)
llvmPutCharOverride =
  let nm = "putchar" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 32
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> KnownBV @32)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callPutChar sym memOps) args)


llvmPutsOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr (EmptyCtx ::> LLVMPointerType wptr) (BVType 32)
llvmPutsOverride =
  let nm = "puts" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callPuts sym memOps) args)


llvmPrintfOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym wptr
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfOverride =
  let nm = "printf" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = True
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> VectorRepr AnyRepr)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callPrintf sym memOps) args)


callMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (LLVMPointerType wptr))
callMalloc sym memOps
           (regValue -> sz) = do
  --liftIO $ putStrLn "MEM MALLOC"
  mem <- readGlobal (llvmMemVar memOps)
  (p, mem') <- liftIO $ doMalloc sym G.HeapAlloc "<malloc>" mem sz
  writeGlobal (llvmMemVar memOps) mem'
  return p


callCalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (LLVMPointerType wptr))
callCalloc sym memOps
           (regValue -> sz)
           (regValue -> num) = do
  --liftIO $ putStrLn "MEM CALLOC"
  mem <- readGlobal (llvmMemVar memOps)
  (p, mem') <- liftIO $ doCalloc sym mem sz num
  writeGlobal (llvmMemVar memOps) mem'
  return p


callFree
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym LLVM r args ret ()
callFree sym memOps
           (regValue -> ptr) = do
  --liftIO $ putStrLn "MEM FREE"
  mem <- readGlobal (llvmMemVar memOps)
  mem' <- liftIO $ doFree sym mem ptr
  writeGlobal (llvmMemVar memOps) mem'


callMemcpy
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym LLVM r args ret ()
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
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym LLVM r args ret ()
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
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 8)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym LLVM r args ret ()
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
  -> LLVMMemOps wptr
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (BVType w))
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


callCtlz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (BVType w))
callCtlz sym _memOps
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       addAssertion sym p (AssertFailureSimError "Ctlz called with disallowed zero value")
       -- FIXME: implement CTLZ as a SimpleBuilder primitive
       go (0 :: Integer)
 where
 w = bvWidth val
 go i
   | i < natValue w =
       do c  <- testBitBV sym (natValue w - i - 1) val
          i' <- bvLit sym w i
          x  <- go $! (i+1)
          bvIte sym c i' x
   | otherwise = bvLit sym w (natValue w)

callPutChar
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (BVType 32)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (BVType 32))
callPutChar _sym _memOps
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (asUnsignedBV ch)
    liftIO $ hPutChar h chval
    return ch


callPuts
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (BVType 32))
callPuts sym memOps
  (regValue -> strPtr) = do
    mem <- readGlobal (llvmMemVar memOps)
    str <- liftIO $ loadString sym mem strPtr Nothing
    h <- printHandle <$> getContext
    liftIO $ hPutStrLn h (UTF8.toString str)
    -- return non-negative value on success
    liftIO $ bvLit sym knownNat 1


callPrintf
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> LLVMMemOps wptr
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType AnyType)
  -> OverrideSim p sym LLVM r args ret (RegValue sym (BVType 32))
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

printfOps :: (IsSymInterface sym, HasPtrWidth wptr)
          => sym
          -> V.Vector (AnyValue sym)
          -> PrintfOperations (StateT (MemImpl sym) IO)
printfOps sym valist =
  PrintfOperations
  { printfGetInteger = \i sgn _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (LLVMPointerRepr _w) x) ->
         do bv <- liftIO (projectLLVM_bv sym x)
            if sgn then
              return $ asSignedBV bv
            else
              return $ asUnsignedBV bv
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
       Just (AnyValue PtrRepr ptr) ->
           do mem <- get
              liftIO $ loadString sym mem ptr numchars
       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected char*, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetPointer = \i ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         return $ show (G.ppPtr ptr)
       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected void*, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfSetInteger = \i len v ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         do mem <- get
            case len of
              Len_Byte  -> do
                 let w8 = knownNat :: NatRepr 8
                 let tp = G.bitvectorType 1
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w8 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr tp (AnyValue (LLVMPointerRepr w8) x)
                 put mem'
              Len_Short -> do
                 let w16 = knownNat :: NatRepr 16
                 let tp = G.bitvectorType 2
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w16 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr tp (AnyValue (LLVMPointerRepr w16) x)
                 put mem'
              Len_NoMod -> do
                 let w32  = knownNat :: NatRepr 32
                 let tp = G.bitvectorType 4
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w32 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr tp (AnyValue (LLVMPointerRepr w32) x)
                 put mem'
              Len_Long  -> do
                 let w64 = knownNat :: NatRepr 64
                 let tp = G.bitvectorType 8
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w64 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr tp (AnyValue (LLVMPointerRepr w64) x)
                 put mem'
              _ ->
                fail $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (AnyValue tpr _) ->
         fail $ unwords ["Type mismatch in printf.  Expected void*, but got:", show tpr]
       Nothing ->
         fail $ unwords ["Out-of-bounds argument access in printf:", show i]
  }
