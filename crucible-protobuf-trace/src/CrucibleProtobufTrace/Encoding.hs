{-# LANGUAGE FunctionalDependencies #-}

module CrucibleProtobufTrace.Encoding (
    ProtoEncoding,
    encodeProto,
)
where

class ProtoEncoding t msg | t -> msg where
    encodeProto :: t -> IO msg
