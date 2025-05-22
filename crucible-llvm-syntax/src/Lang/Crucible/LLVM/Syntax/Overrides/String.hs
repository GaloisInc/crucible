{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Overrides related to C strings
module Lang.Crucible.LLVM.Syntax.Overrides.String
  ( readBytesOverride
  , readCStringOverride
  , writeBytesOverride
  , writeCStringOverride
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.BitVector.Sized qualified as BV
import Data.ByteString qualified as BS
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.NatRepr qualified as DPN
import Data.Text qualified as DT
import Data.Text.Encoding qualified as DTE
import Data.Text.Encoding.Error qualified as DTEE
import Data.Vector qualified as Vec
import Lang.Crucible.Backend qualified as LCB
import Lang.Crucible.LLVM.MemModel qualified as LCLM
import Lang.Crucible.LLVM.MemModel.Strings qualified as LCLMS
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Simulator qualified as LCS
import Lang.Crucible.Types qualified as LCT
import What4.Interface qualified as WI

-- | Override for @read-bytes@.
--
-- The loaded string must be concrete. If a symbolic character is encountered
-- while loading, this function will generate an assertion failure.
readBytesOverride ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.TypedOverride p sym ext (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) (LCT.VectorType (LCT.BVType 8))
readBytesOverride memVar =
  WI.withKnownNat ?ptrWidth $
    LCS.typedOverride (Ctx.uncurryAssignment (readBytes memVar))

-- | Implementation of the @read-bytes@ override.
--
-- The loaded string must be concrete. If a symbolic character is encountered
-- while loading, this function will generate an assertion failure.
readBytes ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.RegValue' sym (LCLM.LLVMPointerType w) ->
  LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCT.VectorType (LCT.BVType 8)))
readBytes memVar ptr =
  LCS.ovrWithBackend $ \bak -> do
    let sym = LCB.backendGetSym bak
    mem <- LCS.readGlobal memVar
    bytes <- liftIO (LCLMS.loadString bak mem (C.unRV ptr) Nothing)
    Vec.fromList <$>
      liftIO (mapM (WI.bvLit sym (DPN.knownNat @8) . BV.word8) bytes)

-- | Override for @read-c-string@.
--
-- Note that:
--
-- * The loaded string must be concrete. If a symbolic character is encountered
--   while loading, this function will generate an assertion failure.
--
-- * The loaded string should be UTF-8–encoded. Any invalid code points in the
--   string will be replaced with the Unicode replacement character @U+FFFD@.
readCStringOverride ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.TypedOverride p sym ext (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w) (LCT.StringType WI.Unicode)
readCStringOverride memVar =
  WI.withKnownNat ?ptrWidth $
    LCS.typedOverride (Ctx.uncurryAssignment (readCString memVar))

-- | Implementation of the @read-c-string@ override.
-- Note that:
--
-- * The loaded string must be concrete. If a symbolic character is encountered
--   while loading, this function will generate an assertion failure.
--
-- * The loaded string should be UTF-8–encoded. Any invalid code points in the
--   string will be replaced with the Unicode replacement character @U+FFFD@.
readCString ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.RegValue' sym (LCLM.LLVMPointerType w) ->
  LCS.OverrideSim p sym ext r args ret (LCS.RegValue sym (LCT.StringType WI.Unicode))
readCString memVar ptr =
  LCS.ovrWithBackend $ \bak -> do
    let sym = LCB.backendGetSym bak
    mem <- LCS.readGlobal memVar
    bytes <- liftIO (LCLMS.loadString bak mem (C.unRV ptr) Nothing)
    let lit = DTE.decodeUtf8With DTEE.lenientDecode (BS.pack bytes)
    liftIO (WI.stringLit sym (WI.UnicodeLiteral lit))

-- | Override for @write-bytes@.
writeBytesOverride ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.TypedOverride p sym ext (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCT.VectorType (LCT.BVType 8)) LCT.UnitType
writeBytesOverride memVar =
  WI.withKnownNat ?ptrWidth $
    LCS.typedOverride (Ctx.uncurryAssignment (writeBytes memVar))

-- | Implementation of the @write-bytes@ override.
writeBytes ::
  ( LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.RegValue' sym (LCLM.LLVMPointerType w) ->
  LCS.RegValue' sym (LCT.VectorType (LCT.BVType 8)) ->
  LCS.OverrideSim p sym ext r args ret ()
writeBytes memVar ptr bytes =
  LCS.ovrWithBackend $ \bak ->
    LCS.modifyGlobal memVar $ \mem -> do
      mem' <- liftIO (LCLMS.storeString bak mem (C.unRV ptr) (C.unRV bytes))
      pure ((), mem')

-- | Override for @write-c-string@.
--
-- Note:
--
-- * The string argument must be concrete. If given a symbolic string, this
--   override will generate an assertion failure.
--
-- * The string will be UTF-8–encoded when written.
writeCStringOverride ::
  ( WI.IsExpr (WI.SymExpr sym)
  , LCB.IsSymInterface sym
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.TypedOverride p sym ext (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w Ctx.::> LCT.StringType WI.Unicode) LCT.UnitType
writeCStringOverride memVar =
  WI.withKnownNat ?ptrWidth $
    LCS.typedOverride (Ctx.uncurryAssignment (writeCString memVar))

-- | Implementation of the @write-c-string@ override.
--
-- Note:
--
-- * The string argument must be concrete. If given a symbolic string, this
--   override will generate an assertion failure.
--
-- * The string will be UTF-8–encoded when written.
writeCString ::
  ( WI.IsExpr (WI.SymExpr sym)
  , LCB.IsSymInterface sym
  , LCLM.HasLLVMAnn sym
  , LCLM.HasPtrWidth w
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  LCS.RegValue' sym (LCLM.LLVMPointerType w) ->
  LCS.RegValue' sym (LCT.StringType WI.Unicode) ->
  LCS.OverrideSim p sym ext r args ret ()
writeCString memVar ptr str =
  case WI.asString (C.unRV str) of
    Just (WI.UnicodeLiteral txt) -> do
      -- Convert any escaped unicode characters into actual unicode
      let txt' = read ("\"" ++ DT.unpack txt ++ "\"") :: String

      -- Convert to bytes and write out
      let bytes = BS.unpack $ DTE.encodeUtf8 $ DT.pack txt'
      LCS.ovrWithBackend $ \bak -> do
        let sym = LCB.backendGetSym bak
        LCS.modifyGlobal memVar $ \mem -> do
          bytes' <- liftIO (mapM (WI.bvLit sym (DPN.knownNat @8) . BV.word8) bytes)
          mem' <- liftIO (LCLMS.storeString bak mem (C.unRV ptr) (Vec.fromList bytes'))
          pure ((), mem')
    Nothing ->
      LCS.overrideError $
        LCS.AssertFailureSimError "Call to @write-c-string with symbolic string" ""
