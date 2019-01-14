-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics
-- Description      : Override definitions for LLVM intrinsic and basic
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
( LLVM
, llvmIntrinsicTypes
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

import           GHC.TypeNats (KnownNat)
import qualified Codec.Binary.UTF8.Generic as UTF8
import           Control.Applicative
import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Bits
import           Data.Foldable( asum )
import qualified Data.List as List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Numeric
import           System.IO
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import           What4.FunctionName
import           What4.Interface
import           What4.Utils.MonadST

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.Utils.MonadVerbosity

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.Pointer
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.Printf
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext


llvmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmIntrinsicTypes =
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_memory") IntrinsicMuxFn $
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn $
   MapF.empty

register_llvm_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a (LLVMContext arch)
register_llvm_overrides llvm_module llvm_ctx =
  flip execStateT llvm_ctx $
    forM_ (L.modDeclares llvm_module) $ \decl ->
      runMaybeT (runReaderT do_register_overrides decl) >> return ()

do_register_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  RegOverrideM p sym arch rtp l a ()
do_register_overrides = do
  llvmctx <- get
  let ?lc = llvmctx^.llvmTypeCtx

  -- LLVM Compiler intrinsics
  asum
   [ register_llvm_override llvmLifetimeStartOverride
   , register_llvm_override llvmLifetimeEndOverride
   , register_llvm_override (llvmLifetimeOverrideOverload "start" (knownNat @8))
   , register_llvm_override (llvmLifetimeOverrideOverload "end" (knownNat @8))
   , register_llvm_override llvmMemcpyOverride_8_8_32
   , register_llvm_override llvmMemcpyOverride_8_8_64
   , register_llvm_override llvmMemmoveOverride_8_8_32
   , register_llvm_override llvmMemmoveOverride_8_8_64
   , register_llvm_override llvmMemsetOverride_8_32
   , register_llvm_override llvmMemsetOverride_8_64

   , register_llvm_override llvmObjectsizeOverride_32
   , register_llvm_override llvmObjectsizeOverride_64

   , register_llvm_override llvmObjectsizeOverride_32'
   , register_llvm_override llvmObjectsizeOverride_64'

   , register_llvm_override llvmStacksave
   , register_llvm_override llvmStackrestore

   , register_1arg_polymorphic_override "llvm.ctlz" (\w -> SomeLLVMOverride (llvmCtlz w))
   , register_1arg_polymorphic_override "llvm.cttz" (\w -> SomeLLVMOverride (llvmCttz w))
   , register_1arg_polymorphic_override "llvm.ctpop" (\w -> SomeLLVMOverride (llvmCtpop w))
   , register_1arg_polymorphic_override "llvm.bitreverse" (\w -> SomeLLVMOverride (llvmBitreverse w))

   , register_llvm_override (llvmBSwapOverride (knownNat @2))  -- 16 = 2 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @4))  -- 32 = 4 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @6))  -- 48 = 6 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @8))  -- 64 = 8 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @10)) -- 80 = 10 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @12)) -- 96 = 12 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @14)) -- 112 = 14 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @16)) -- 128 = 16 * 8

   , register_1arg_polymorphic_override "llvm.sadd.with.overflow"
       (\w -> SomeLLVMOverride (llvmSaddWithOverflow w))
   , register_1arg_polymorphic_override "llvm.uadd.with.overflow"
       (\w -> SomeLLVMOverride (llvmUaddWithOverflow w))
   , register_1arg_polymorphic_override "llvm.ssub.with.overflow"
       (\w -> SomeLLVMOverride (llvmSsubWithOverflow w))
   , register_1arg_polymorphic_override "llvm.usub.with.overflow"
       (\w -> SomeLLVMOverride (llvmUsubWithOverflow w))
   , register_1arg_polymorphic_override "llvm.smul.with.overflow"
       (\w -> SomeLLVMOverride (llvmSmulWithOverflow w))
   , register_1arg_polymorphic_override "llvm.umul.with.overflow"
       (\w -> SomeLLVMOverride (llvmUmulWithOverflow w))

    -- C standard library functions
   , register_llvm_override llvmAssertRtnOverride
   , register_llvm_override llvmMemcpyOverride
   , register_llvm_override llvmMemcpyChkOverride
   , register_llvm_override llvmMemmoveOverride
   , register_llvm_override llvmMemsetOverride
   , register_llvm_override llvmMemsetChkOverride
   , register_llvm_override llvmMallocOverride
   , register_llvm_override llvmCallocOverride
   , register_llvm_override llvmFreeOverride
   , register_llvm_override llvmReallocOverride
   , register_llvm_override llvmStrlenOverride
   , register_llvm_override llvmPrintfOverride
   , register_llvm_override llvmPutsOverride
   , register_llvm_override llvmPutCharOverride

   -- Some architecture-dependent intrinsics
   , register_llvm_override llvmX86_SSE2_storeu_dq
   , register_llvm_override llvmX86_pclmulqdq
   ]
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
data LLVMContext arch
   = LLVMContext
   { -- | Map LLVM symbols to their associated state.
     _symbolMap     :: !SymbolHandleMap
   , llvmArch       :: ArchRepr arch
   , llvmPtrWidth   :: forall a. (16 <= (ArchWidth arch) => NatRepr (ArchWidth arch) -> a) -> a
   , llvmMemVar     :: GlobalVar Mem
   , _llvmTypeCtx   :: TypeContext
   }

symbolMap :: Simple Lens (LLVMContext arch) SymbolHandleMap
symbolMap = lens _symbolMap (\s v -> s { _symbolMap = v })

llvmTypeCtx :: Simple Lens (LLVMContext arch) TypeContext
llvmTypeCtx = lens _llvmTypeCtx (\s v -> s{ _llvmTypeCtx = v })

mkLLVMContext :: HandleAllocator s
              -> L.Module
              -> ST s (Some LLVMContext)
mkLLVMContext halloc m = do
  let (errs, typeCtx) = typeContextFromModule m
  unless (null errs) $
    fail $ unlines
         $ [ "Failed to construct LLVM type context:" ] ++ map show errs
  let dl = llvmDataLayout typeCtx

  case someNat (toInteger (ptrBitwidth dl)) of
    Just (Some (wptr :: NatRepr wptr)) | Just LeqProof <- testLeq (knownNat @16) wptr ->
      withPtrWidth wptr $
        do mvar <- mkMemVar halloc
           let archRepr = X86Repr wptr -- FIXME! we should select the architecture based on
                                       -- the target triple, but llvm-pretty doesn't capture this
                                       -- currently.
           let ctx :: LLVMContext (X86 wptr)
               ctx = LLVMContext
                     { _symbolMap = Map.empty
                     , llvmArch     = archRepr
                     , llvmMemVar   = mvar
                     , llvmPtrWidth = \x -> x wptr
                     , _llvmTypeCtx = typeCtx
                     }
           return (Some ctx)
    _ ->
      fail ("Cannot load LLVM bitcode file with illegal pointer width: " ++ show (dl^.ptrSize))

-- | This type represents an implementation of an LLVM intrinsic function in
-- Crucible.
data LLVMOverride p sym arch args ret =
  LLVMOverride
  { llvmOverride_declare :: L.Declare -- ^ An LLVM name and signature for this intrinsic
  , llvmOverride_args :: CtxRepr args -- ^ A representation of the argument types
  , llvmOverride_ret  :: TypeRepr ret -- ^ A representation of the return type
  , llvmOverride_def ::
       forall rtp args' ret'.
         GlobalVar Mem ->
         sym ->
         Ctx.Assignment (RegEntry sym) args ->
         OverrideSim p sym (LLVM arch) rtp args' ret' (RegValue sym ret)
    -- ^ The implementation of the intrinsic in the simulator monad
    -- (@OverrideSim@).
  }

data SomeLLVMOverride p sym arch =
  forall args ret. SomeLLVMOverride (LLVMOverride p sym arch args ret)

newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall arch rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym (LLVM arch) rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall arch rtp l a.
    RegValue sym tp ->
    OverrideSim p sym (LLVM arch) rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall m p sym args args'.
  (IsSymInterface sym, Monad m) =>
  sym ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym args args')
transformLLVMArgs _ Empty Empty =
  return (ArgTransformer (\_ -> return Ctx.Empty))
transformLLVMArgs sym (rest' :> tp') (rest :> tp) = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformLLVMRet sym tp tp'
                 (ArgTransformer fs) <- transformLLVMArgs sym rest' rest
                 xs' <- fs xs
                 x'  <- RegEntry tp' <$> f (regValue x)
                 pure (xs' :> x')))
transformLLVMArgs _ _ _ =
  panic "Intrinsics.transformLLVMArgs"
    [ "transformLLVMArgs: argument shape mismatch!" ]

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
transformLLVMRet sym (VectorRepr tp) (VectorRepr tp')
  = do ValTransformer f <- transformLLVMRet sym tp tp'
       return (ValTransformer (traverse f))
transformLLVMRet sym (StructRepr ctx) (StructRepr ctx')
  = do ArgTransformer tf <- transformLLVMArgs sym ctx' ctx
       return (ValTransformer (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

transformLLVMRet _sym ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformLLVMRet _sym ret ret'
  = panic "Intrinsics.transformLLVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the LLVM calling convention.  This basically just coerces
--   between values of @BVType w@ and values of @LLVMPointerType w@.
build_llvm_override ::
  IsSymInterface sym =>
  sym ->
  FunctionName ->
  CtxRepr args ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall rtp' l' a'. Ctx.Assignment (RegEntry sym) args ->
   OverrideSim p sym (LLVM arch) rtp' l' a' (RegValue sym ret)) ->
  OverrideSim p sym (LLVM arch) rtp l a (Override p sym (LLVM arch) args' ret')
build_llvm_override sym fnm args ret args' ret' llvmOverride =
  do fargs <- transformLLVMArgs sym args args'
     fret  <- transformLLVMRet  sym ret  ret'
     return $ mkOverride' fnm ret' $
            do RegMap xs <- getOverrideArgs
               applyValTransformer fret =<< llvmOverride =<< applyArgTransformer fargs xs


type RegOverrideM p sym arch rtp l a =
  ReaderT L.Declare (MaybeT (StateT (LLVMContext arch) (OverrideSim p sym (LLVM arch) rtp l a)))


register_1arg_polymorphic_override :: forall p sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym arch) ->
  RegOverrideM p sym arch rtp l a ()
register_1arg_polymorphic_override prefix overrideFn =
  do L.Symbol nm <- L.decName <$> ask
     case List.stripPrefix prefix nm of
       Just ('.':'i': (readDec -> (sz,[]):_))
         | Just (Some w) <- someNat sz
         , Just LeqProof <- isPosNat w
         -> case overrideFn w of SomeLLVMOverride ovr -> register_llvm_override ovr
       _ -> empty

register_llvm_override :: forall p args ret sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMOverride p sym arch args ret ->
  RegOverrideM p sym arch rtp l a ()
register_llvm_override llvmOverride = do
  requestedDecl <- ask
  llvmctx <- get
  let decl = llvmOverride_declare llvmOverride

  if (requestedDecl /= decl) then
    do when (L.decName requestedDecl == L.decName decl) $
         do logFn <- lift $ lift $ lift $ getLogFunction
            liftIO $ logFn 3 $ unwords
              [ "Mismatched declaration signatures"
              , " *** requested: " ++ show requestedDecl
              , " *** found: "     ++ show decl
              , ""
              ]
       empty
  else
   do let nm@(L.Symbol str_nm) = L.decName decl
      let fnm  = functionNameFromText (Text.pack str_nm)

      sym <- lift $ lift $ lift $ getSymInterface

      let mvar = llvmMemVar llvmctx
      let overrideArgs = llvmOverride_args llvmOverride
      let overrideRet  = llvmOverride_ret llvmOverride

      let ?lc = llvmctx^.llvmTypeCtx

      decl' <- either fail return $ liftDeclare decl
      llvmDeclToFunHandleRepr decl' $ \derivedArgs derivedRet -> do
        o <- lift $ lift $ lift $ build_llvm_override sym fnm overrideArgs overrideRet derivedArgs derivedRet
                      (llvmOverride_def llvmOverride mvar sym)
        case Map.lookup nm (llvmctx^.symbolMap) of
          Just (LLVMHandleInfo _decl' h) -> do
            case testEquality (handleArgTypes h) derivedArgs of
               Nothing ->
                 panic "Intrinsics.register_llvm_override"
                   [ "Argument type mismatch when registering LLVM mss override."
                   , "*** Override name: " ++ show nm
                   , "*** Declared type: " ++ show (handleArgTypes h)
                   , "*** Expected type: " ++ show derivedArgs
                   ]
               Just Refl ->
                 case testEquality (handleReturnType h) derivedRet of
                   Nothing ->
                     panic "Intrinsics.register_llvm_override"
                       [ "return type mismatch when registering LLVM mss override"
                       , "*** Override name: " ++ show nm
                       ]
                   Just Refl -> lift $ lift $ lift $ bindFnHandle h (UseOverride o)
          Nothing ->
            do ctx <- lift $ lift $ lift $ use stateContext
               let ha = simHandleAllocator ctx
               h <- lift $ lift $ liftST $ mkHandle' ha fnm derivedArgs derivedRet
               lift $ lift $ lift $ bindFnHandle h (UseOverride o)
               put (llvmctx & symbolMap %~ Map.insert nm (LLVMHandleInfo decl h))


-- | Convenient LLVM representation of the @size_t@ type.
llvmSizeT :: HasPtrWidth wptr => L.Type
llvmSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

-- | This intrinsic is currently a no-op.
--
-- We might want to support this in the future to catch undefined memory
-- accesses.
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-start-intrinsic LLVM docs>
llvmLifetimeStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
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

-- | See comment on 'llvmLifetimeStartOverride'
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-end-intrinsic LLVM docs>
llvmLifetimeEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
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

-- | This is a no-op.
--
-- The language reference doesn't mention the use of this intrinsic.
llvmLifetimeOverrideOverload
  :: forall width sym wptr arch p
   . ( 1 <= width, KnownNat width
     , IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => String -- ^ "start" or "end"
  -> NatRepr width
  -> LLVMOverride p sym arch
        (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
        UnitType -- It appears in practice that this is always void
llvmLifetimeOverrideOverload startOrEnd widthRepr =
  let
    width' :: Int
    width' = widthVal widthRepr
    nm = "llvm.lifetime." ++ startOrEnd ++ ".p0i" ++ show width'
  in LLVMOverride
      ( L.Declare
        { L.decRetType = L.PrimType $ L.Void
        , L.decName    = L.Symbol nm
        , L.decArgs    = [ L.PrimType $ L.Integer $ 64
                         , L.PtrTo $ L.PrimType $ L.Integer $ fromIntegral width'
                         ]
        , L.decVarArgs = False
        , L.decAttrs   = []
        , L.decComdat  = mempty
        }
      )
      (Empty :> KnownBV @64 :> PtrRepr)
      UnitRepr
      (\_ops _sym _args -> return ())

llvmStacksave
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch EmptyCtx (LLVMPointerType wptr)
llvmStacksave =
  let nm = "llvm.stacksave" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Integer 8
    , L.decName    = L.Symbol nm
    , L.decArgs    = [
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  Empty
  PtrRepr
  (\_memOps sym _args -> liftIO (mkNullPointer sym PtrWidth))


llvmStackrestore
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) UnitType
llvmStackrestore =
  let nm = "llvm.stackrestore" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr)
  UnitRepr
  (\_memOps _sym _args -> return ())


llvmObjectsizeOverride_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 32)
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

llvmObjectsizeOverride_32'
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32' =
  let nm = "llvm.objectsize.i32.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1 :> KnownBV @1)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize' sym memOps knownNat) args)

llvmObjectsizeOverride_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 64)
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

llvmObjectsizeOverride_64'
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64' =
  let nm = "llvm.objectsize.i64.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 64
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1 :> KnownBV @1)
  (KnownBV @64)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize' sym memOps knownNat) args)

llvmAssertRtnOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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
          liftIO $ assert sym (falsePred sym) err
  )

llvmCallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => LLVMOverride p sym arch
         (EmptyCtx ::> BVType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmCallocOverride =
  let nm = "calloc" in
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Integer 8
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
  (\memOps sym args -> Ctx.uncurryAssignment (callCalloc sym memOps alignment) args)


llvmReallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmReallocOverride =
  let nm = "realloc" in
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Integer 8
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> SizeT)
  (PtrRepr)
  (\memOps sym args -> Ctx.uncurryAssignment (callRealloc sym memOps alignment) args)

llvmMallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => LLVMOverride p sym arch
         (EmptyCtx ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMallocOverride =
  let nm = "malloc" in
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Integer 8
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
  (\memOps sym args -> Ctx.uncurryAssignment (callMalloc sym memOps alignment) args)

llvmFreeOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr)
         UnitType
llvmFreeOverride =
  let nm = "free" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (LLVMPointerType wptr)
llvmMemcpyOverride =
  let nm = "memcpy" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType (L.Integer 8)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType (L.Integer 8)
                     , L.PtrTo $ L.PrimType (L.Integer 8)
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> LLVMPointerType wptr
                   ::> BVType wptr
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemcpyChkOverride =
  let nm = "__memcpy_chk" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType (L.Integer 8)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType (L.Integer 8)
                     , L.PtrTo $ L.PrimType (L.Integer 8)
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> (LLVMPointerType wptr)
                   ::> (LLVMPointerType wptr)
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemmoveOverride =
  let nm = "memmove" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType (L.Integer 8)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType (L.Integer 8)
                     , L.PtrTo $ L.PrimType (L.Integer 8)
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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


llvmSaddWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSaddWithOverflow w =
  let nm = "llvm.sadd.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callSaddWithOverflow sym memOps) args)


llvmUaddWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUaddWithOverflow w =
  let nm = "llvm.uadd.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callUaddWithOverflow sym memOps) args)


llvmSsubWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSsubWithOverflow w =
  let nm = "llvm.ssub.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callSsubWithOverflow sym memOps) args)


llvmUsubWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUsubWithOverflow w =
  let nm = "llvm.usub.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callUsubWithOverflow sym memOps) args)

llvmSmulWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSmulWithOverflow w =
  let nm = "llvm.smul.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callSmulWithOverflow sym memOps) args)

llvmUmulWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUmulWithOverflow w =
  let nm = "llvm.umul.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callUmulWithOverflow sym memOps) args)


llvmCtlz
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCtlz w =
  let nm = "llvm.ctlz.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromInteger (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> KnownBV @1)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callCtlz sym memOps) args)


llvmCttz
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCttz w =
  let nm = "llvm.cttz.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromInteger (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> KnownBV @1)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callCttz sym memOps) args)

llvmCtpop
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmCtpop w =
  let nm = "llvm.ctpop.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromInteger (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callCtpop sym memOps) args)

llvmBitreverse
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmBitreverse w =
  let nm = "llvm.bitreverse.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromInteger (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromInteger (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callBitreverse sym memOps) args)


-- | <https://llvm.org/docs/LangRef.html#llvm-bswap-intrinsics LLVM docs>
llvmBSwapOverride
  :: forall width sym wptr arch p
   . ( 1 <= width, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr width
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType (width * 8))
         (BVType (width * 8))
llvmBSwapOverride widthRepr =
  let width8 = natMultiply widthRepr (knownNat @8)
      width' :: Int
      width' = widthVal width8
      nm = "llvm.bswap.i" ++ show width'
  in
    case mulComm widthRepr (knownNat @8) of { Refl ->
    case leqMulMono (knownNat @8) widthRepr :: LeqProof width (width * 8) of { LeqProof ->
    case leqTrans (LeqProof :: LeqProof 1 width)
                  (LeqProof :: LeqProof width (width * 8)) of { LeqProof ->
      LLVMOverride
        ( -- From the LLVM docs:
          -- declare i16 @llvm.bswap.i16(i16 <id>)
          L.Declare
          { L.decRetType = L.PrimType $ L.Integer $ fromIntegral width'
          , L.decName    = L.Symbol nm
          , L.decArgs    = [ L.PrimType $ L.Integer $ fromIntegral width' ]
          , L.decVarArgs = False
          , L.decAttrs   = []
          , L.decComdat  = mempty
          }
        )
        (Empty :> BVRepr width8)
        (BVRepr width8)
        (\_ sym args -> liftIO $
            let vec :: SymBV sym (width * 8)
                vec = regValue (args^._1)
            in bvSwap sym widthRepr vec)
    }}}


llvmX86_pclmulqdq
--declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) #1
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> VectorType (BVType 64)
                   ::> VectorType (BVType 64)
                   ::> BVType 8)
         (VectorType (BVType 64))
llvmX86_pclmulqdq =
  let nm = "llvm.x86.pclmulqdq" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Vector 2 (L.PrimType $ L.Integer 64)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.Vector 2 (L.PrimType $ L.Integer 64)
                     , L.Vector 2 (L.PrimType $ L.Integer 64)
                     , L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> VectorRepr (KnownBV @64) :> VectorRepr (KnownBV @64) :> KnownBV @8)
  (VectorRepr (KnownBV @64))
  (\memOps sym args -> Ctx.uncurryAssignment (callX86_pclmulqdq sym memOps) args)


llvmX86_SSE2_storeu_dq
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType (BVType 8))
         UnitType
llvmX86_SSE2_storeu_dq =
  let nm = "llvm.x86.sse2.storeu.dq" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.Vector 16 (L.PrimType $ L.Integer 8)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> VectorRepr (KnownBV @8))
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callStoreudq sym memOps) args)


llvmMemsetOverride_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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


llvmMemsetOverride :: forall p sym arch wptr.
     (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType 32
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetOverride =
  let nm = "memset" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType (L.Integer 8)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType (L.Integer 8)
                     , L.PrimType $ L.Integer 32
                     , llvmSizeT
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @32 :> SizeT)
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                 ::> BVType 32
                 ::> BVType wptr
                 ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetChkOverride =
  let nm = "__memset_chk" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType (L.Integer 8)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType (L.Integer 8)
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 32) (BVType 32)
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
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) (BVType 32)
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

llvmStrlenOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) (BVType wptr)
llvmStrlenOverride =
  let nm = "strlen" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = llvmSizeT
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr)
  SizeT
  (\memOps sym args -> Ctx.uncurryAssignment (callStrlen sym memOps) args)

llvmPrintfOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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


callRealloc
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (LLVMPointerType wptr))
callRealloc sym mvar alignment (regValue -> ptr) (regValue -> sz) =
  do szZero  <- liftIO (notPred sym =<< bvIsNonzero sym sz)
     ptrNull <- liftIO (ptrIsNull sym PtrWidth ptr)
     symbolicBranches emptyRegMap
       -- If the pointer is null, behave like malloc
       [ (ptrNull
         , do mem <- readGlobal mvar
              (newp, mem') <- liftIO $ doMalloc sym G.HeapAlloc G.Mutable "<realloc>" mem sz alignment
              writeGlobal mvar mem'
              return newp
         ,
         Nothing)

       -- If the size is zero, behave like malloc (of zero bytes) then free
       , (szZero
         , do mem <- readGlobal mvar
              (newp, mem') <- liftIO $
                do (newp, mem1) <- doMalloc sym G.HeapAlloc G.Mutable "<realloc>" mem sz alignment
                   mem2 <- doFree sym Nothing mem1 ptr
                   return (newp, mem2)
              writeGlobal mvar mem'
              return newp
         , Nothing
         )

       -- Otherwise, allocate a new region, memcopy `sz` bytes and free the old pointer
       , (truePred sym
         , do mem  <- readGlobal mvar
              (newp, mem') <- liftIO $
                do (newp, mem1) <- doMalloc sym G.HeapAlloc G.Mutable "<realloc>" mem sz alignment
                   mem2 <- uncheckedMemcpy sym mem1 newp ptr sz
                   mem3 <- doFree sym Nothing mem2 ptr
                   return (newp, mem3)
              writeGlobal mvar mem'
              return newp
         , Nothing)
       ]


callMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (LLVMPointerType wptr))
callMalloc sym mvar alignment
           (regValue -> sz) = do
  --liftIO $ putStrLn "MEM MALLOC"
  mem <- readGlobal mvar
  (p, mem') <- liftIO $ doMalloc sym G.HeapAlloc G.Mutable "<malloc>" mem sz alignment
  writeGlobal mvar mem'
  return p


callCalloc
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (LLVMPointerType wptr))
callCalloc sym mvar alignment
           (regValue -> sz)
           (regValue -> num) = do
  --liftIO $ putStrLn "MEM CALLOC"
  mem <- readGlobal mvar
  (p, mem') <- liftIO $ doCalloc sym mem sz num alignment
  writeGlobal mvar mem'
  return p


callFree
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callFree sym mvar
           (regValue -> ptr) = do
  --liftIO $ putStrLn "MEM FREE"
  mem <- readGlobal mvar
  mem' <- liftIO $ doFree sym Nothing mem ptr
  writeGlobal mvar mem'


callMemcpy
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callMemcpy sym mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _align _volatile = do
  -- FIXME? add assertions about alignment
  --liftIO $ putStrLn "MEM COPY"
  mem <- readGlobal mvar
  liftIO $ assertDisjointRegions sym w dest src len
  mem' <- liftIO $ doMemcpy sym w mem dest src len
  writeGlobal mvar mem'

-- NB the only difference between memcpy and memove
-- is that memmove does not assert that the memory
-- ranges are disjoint.  The underlying operation
-- works correctly in both cases.
callMemmove
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callMemmove sym mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _align _volatile = do
  -- FIXME? add assertions about alignment
  --liftIO $ putStrLn "MEM MOVE"
  mem <- readGlobal mvar
  mem' <- liftIO $ doMemcpy sym w mem dest src len
  writeGlobal mvar mem'


callMemset
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 8)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 32)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callMemset sym mvar
           (regValue -> dest)
           (regValue -> val)
           (RegEntry (BVRepr w) len)
           _align _volatile = do
  -- FIXME? add assertions about alignment
  --liftIO $ putStrLn "MEM SET"
  mem <- readGlobal mvar
  mem' <- liftIO $ doMemset sym Nothing w mem dest val len
  writeGlobal mvar mem'


callX86_pclmulqdq :: forall p sym arch wptr r args ret.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  sym ->
  GlobalVar Mem ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (BVType 8) ->
  OverrideSim p sym (LLVM arch) r args ret (RegValue sym (VectorType (BVType 64)))
callX86_pclmulqdq sym _mvar
  (regValue -> xs)
  (regValue -> ys)
  (regValue -> imm) =
    do unless (V.length xs == 2) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
           ["Vector length mismatch in llvm.x86.pclmulqdq intrinsic"
           ,"Expected <2 x i64>, but got vector of length ", show (V.length xs)
           ]
       unless (V.length ys == 2) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
           ["Vector length mismatch in llvm.x86.pclmulqdq intrinsic"
           ,"Expected <2 x i64>, but got vector of length ", show (V.length ys)
           ]
       case asUnsignedBV imm of
         Just byte ->
           do let xidx = if byte .&. 0x01 == 0 then 0 else 1
              let yidx = if byte .&. 0x10 == 0 then 0 else 1
              liftIO $ doPcmul (xs V.! xidx) (ys V.! yidx)
         _ ->
             liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
                ["Illegal selector argument to llvm.x86.pclmulqdq"
                ,"  Expected concrete value but got ", show (printSymExpr imm)
                ]
  where
  doPcmul :: SymBV sym 64 -> SymBV sym 64 -> IO (V.Vector (SymBV sym 64))
  doPcmul x y =
    do r <- carrylessMultiply sym x y
       lo <- bvTrunc sym (knownNat @64) r
       hi <- bvSelect sym (knownNat @64) (knownNat @64) r
       -- NB, little endian because X86
       return $ V.fromList [ lo, hi ]

callStoreudq
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType (BVType 8))
  -> OverrideSim p sym (LLVM arch) r args ret ()
callStoreudq sym mvar
  (regValue -> dest)
  (regValue -> vec) =
    do mem <- readGlobal mvar
       unless (V.length vec == 16) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
           ["Vector length mismatch in stored_qu intrinsic."
           ,"Expected <16 x i8>, but got vector of length ", show (V.length vec)
           ]
       mem' <- liftIO $ doStore
                 sym
                 mem
                 dest
                 (VectorRepr (KnownBV @8))
                 (arrayType 16 (bitvectorType (Bytes 1)))
                 noAlignment
                 vec
       writeGlobal mvar mem'


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
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize sym _mvar w
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

callObjectsize'
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize' sym mvar w ptr flag _nullKnown = callObjectsize sym mvar w ptr flag


callCtlz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCtlz sym _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       assert sym p (AssertFailureSimError "Ctlz called with disallowed zero value")
       bvCountLeadingZeros sym val

callSaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSaddWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- addSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUaddWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- addUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUsubWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- subUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callSsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSsubWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- subSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callSmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSmulWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- mulSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUmulWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- mulUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')


callCttz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCttz sym _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       assert sym p (AssertFailureSimError "Cttz called with disallowed zero value")
       bvCountTrailingZeros sym val

callCtpop
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCtpop sym _mvar
  (regValue -> val) = liftIO $ bvPopcount sym val

callBitreverse
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callBitreverse sym _mvar
  (regValue -> val) = liftIO $ bvBitreverse sym val


callPutChar
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType 32)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPutChar _sym _mvar
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (asUnsignedBV ch)
    liftIO $ hPutChar h chval
    return ch


callPuts
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPuts sym mvar
  (regValue -> strPtr) = do
    mem <- readGlobal mvar
    str <- liftIO $ loadString sym mem strPtr Nothing
    h <- printHandle <$> getContext
    liftIO $ hPutStrLn h (UTF8.toString str)
    -- return non-negative value on success
    liftIO $ bvLit sym knownNat 1

callStrlen
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType wptr))
callStrlen sym mvar (regValue -> strPtr) = do
  mem <- readGlobal mvar
  len <- liftIO $ length <$> loadString sym mem strPtr Nothing
  liftIO $ bvLit sym ?ptrWidth (fromIntegral len)

callPrintf
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType AnyType)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPrintf sym mvar
  (regValue -> strPtr)
  (regValue -> valist) = do
    mem <- readGlobal mvar
    formatStr <- liftIO $ loadString sym mem strPtr Nothing
    case parseDirectives formatStr of
      Left err -> overrideError $ AssertFailureSimError err
      Right ds -> do
        ((str, n), mem') <- liftIO $ runStateT (executeDirectives (printfOps sym valist) ds) mem
        writeGlobal mvar mem'
        h <- printHandle <$> getContext
        liftIO $ hPutStr h str
        liftIO $ bvLit sym knownNat (toInteger n)

printfOps :: (IsSymInterface sym, HasPtrWidth wptr)
          => sym
          -> V.Vector (AnyValue sym)
          -> PrintfOperations (StateT (MemImpl sym) IO)
printfOps sym valist =
  PrintfOperations
  { printfUnsupported = \x -> lift $ addFailedAssertion sym
                                   $ Unsupported x

  , printfGetInteger = \i sgn _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (LLVMPointerRepr _w) x) ->
         do bv <- liftIO (projectLLVM_bv sym x)
            if sgn then
              return $ asSignedBV bv
            else
              return $ asUnsignedBV bv
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords ["Type mismatch in printf.  Expected integer, but got:"
                        , show tpr]
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetFloat = \i _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (FloatRepr _fi) _x) ->
         -- TODO: handle interpreted floats
         return Nothing
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords [ "Type mismatch in printf."
                        , "Expected floating-point, but got:", show tpr]
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetString  = \i numchars ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
           do mem <- get
              liftIO $ loadString sym mem ptr numchars
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords [ "Type mismatch in printf."
                        , "Expected char*, but got:", show tpr]
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfGetPointer = \i ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         return $ show (G.ppPtr ptr)
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords [ "Type mismatch in printf."
                        , "Expected void*, but got:", show tpr]
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords ["Out-of-bounds argument access in printf:", show i]

  , printfSetInteger = \i len v ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         do mem <- get
            case len of
              Len_Byte  -> do
                 let w8 = knownNat :: NatRepr 8
                 let tp = G.bitvectorType 1
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w8 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w8) tp noAlignment x
                 put mem'
              Len_Short -> do
                 let w16 = knownNat :: NatRepr 16
                 let tp = G.bitvectorType 2
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w16 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w16) tp noAlignment x
                 put mem'
              Len_NoMod -> do
                 let w32  = knownNat :: NatRepr 32
                 let tp = G.bitvectorType 4
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w32 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w32) tp noAlignment x
                 put mem'
              Len_Long  -> do
                 let w64 = knownNat :: NatRepr 64
                 let tp = G.bitvectorType 8
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w64 (toInteger v))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w64) tp noAlignment x
                 put mem'
              _ ->
                lift $ addFailedAssertion sym
                     $ Unsupported
                     $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords [ "Type mismatch in printf."
                        , "Expected void*, but got:", show tpr]

       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
              $ unwords ["Out-of-bounds argument access in printf:", show i]
  }
