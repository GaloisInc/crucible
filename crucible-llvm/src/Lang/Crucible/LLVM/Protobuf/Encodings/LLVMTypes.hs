{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Lang.Crucible.LLVM.Protobuf.Encodings.LLVMTypes (
)
where

import           Data.ProtoLens (defMessage)
import           Data.ProtoLens.Prism
import           Lens.Micro ((&), (.~), (?~))
import           What4.Expr.Builder
import           What4.Interface
import           Data.Word (Word64, Word32)
import           Lang.Crucible.LLVM.DataLayout (fromAlignment)
import           Lang.Crucible.LLVM.Bytes

-- import ProtoEncoding and SymExprWrapper helper
import           CrucibleProtobufTrace.Encoding
import           CrucibleProtobufTrace.What4Encodings

-- import Protobuf types
import qualified CrucibleProtobufTrace.ProtoDefs.MemoryEvents as ProtoM
import qualified CrucibleProtobufTrace.ProtoDefs.MemoryState as ProtoMS
import qualified CrucibleProtobufTrace.ProtoDefs.LlvmVal as ProtoLLVM

-- import the types being serialized
import qualified Lang.Crucible.LLVM.MemModel as CrucibleM
import qualified Lang.Crucible.LLVM.MemModel.MemLog as CrucibleM
import qualified Lang.Crucible.LLVM.DataLayout as CrucibleM
import Lang.Crucible.Panic (Crucible)

instance (sym ~ (ExprBuilder s t st)) => ProtoEncoding (CrucibleM.WriteSource sym w) ProtoMS.WriteSource where
    encodeProto (CrucibleM.MemCopy src len) = do
        src <- encodeProto src
        len <- encodeProto (SymExprWrapper len)
        return
            $ defMessage
                & ProtoMS.maybe'srcMemCopy .~
                    _Just # (defMessage
                        & ProtoMS.addr .~ src
                        & ProtoMS.size .~ len
                    )

    encodeProto (CrucibleM.MemStore val storage_type alignment) = do
        v <- encodeProto val
        st <- encodeProto storage_type
        algn <- encodeProto alignment
        return
            $ defMessage
                & ProtoMS.maybe'srcMemStore .~ _Just # (
                    defMessage
                        & ProtoMS.value .~ v
                        & ProtoMS.storageType .~ st
                        & ProtoMS.byteAlignment .~ algn
                )

    encodeProto (CrucibleM.MemSet val len) = do
        val' <- encodeProto (SymExprWrapper val)
        len' <- encodeProto (SymExprWrapper len)
        return
            $ defMessage
                & ProtoMS.maybe'srcMemSet .~ _Just # (
                    defMessage
                        & ProtoMS.fillByteVal .~ val'
                        & ProtoMS.size .~ len'
                )

    encodeProto (CrucibleM.MemArrayStore _array _maybe_bv) = undefined -- we don't handle this for now

    encodeProto (CrucibleM.MemInvalidate text len) = do
        len' <- encodeProto (SymExprWrapper len)
        return
            $ defMessage
                & ProtoMS.maybe'srcInvalidate .~ _Just # (
                    defMessage
                        & ProtoMS.message .~ text
                        & ProtoM.size .~ len'
                )

-- instance implementing ProtoEncoding for MemWrite


-- instance (sym ~ (ExprBuilder s t st)) => ProtoEncoding (CrucibleM.MemWrite sym) ProtoM.MemoryEventWrite where
--     encodeProto (CrucibleM.MemWrite addr src) = do
--         addr <- encodeProto addr
--         src <- encodeProto src
--         return
--             $ defMessage
--                 & ProtoM.dst .~ addr
--                 & ProtoM.src .~ src
--     -- We'll just never have to create these because we should be able to reconstruct them from the trace and the merges
--     encodeProto (CrucibleM.WriteMerge pred lhs rhs) = do
--         return undefined
