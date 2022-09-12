{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Lang.Crucible.Protobuf.Encodings.Abort (
)
where

import Control.Lens
import Data.ProtoLens (Message(defMessage))

import CrucibleProtobufTrace.Encoding
import CrucibleProtobufTrace.What4Encodings
import qualified CrucibleProtobufTrace.ProtoDefs.Abort as ProtoA
import Lang.Crucible.Simulator.ExecutionTree (AbortedResult (AbortedExec, AbortedExit, AbortedBranch))
import System.Exit (ExitCode(ExitSuccess, ExitFailure))
import Data.Text (pack)


instance ProtoEncoding (AbortedResult sym ext) ProtoA.AbortedResult where
    encodeProto (AbortedExec rsn frm) = do
        return
            $ defMessage
                & ProtoA.maybe'abortSingle .~ _Just # (
                    defMessage
                        & ProtoA.reason .~ (pack $ show rsn)
                )

    encodeProto (AbortedExit ExitSuccess) = do
        return
            $ defMessage
                & ProtoA.maybe'abortExit .~ _Just # (
                    defMessage
                        & ProtoA.exitSuccess .~ True
                )
    encodeProto (AbortedExit (ExitFailure code)) = do
        return
            $ defMessage
                & ProtoA.maybe'abortExit .~ _Just # (
                    defMessage
                        & ProtoA.exitSuccess .~ False
                        & ProtoA.exitCode .~ (fromIntegral code)
                )

    encodeProto (AbortedBranch loc pred resultTrue resultFalse) = do
        return undefined