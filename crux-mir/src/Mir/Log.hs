{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module Mir.Log
  ( MirLogMessage (..),
    SupportsMirLogMessage,
    mirLogMessageToSayWhat,
    sayMir,
  )
where

import Data.Aeson (ToJSON)
import qualified Data.Text as T
import GHC.Generics (Generic)

import Crux.Log (SayLevel (..), SayWhat (..))
import qualified Crux.Log as Log

data MirLogMessage
  = FinalResults
  deriving (Generic, ToJSON)

type SupportsMirLogMessage msgs =
  (?injectMirLogMessage :: MirLogMessage -> msgs)

sayMir ::
  Log.Logs msgs =>
  SupportsMirLogMessage msgs =>
  MirLogMessage ->
  IO ()
sayMir msg =
  let ?injectMessage = ?injectMirLogMessage
   in Log.say msg

cruxMirLogTag :: T.Text
cruxMirLogTag = "Crux-MIR"

simply :: T.Text -> SayWhat
simply = SayWhat Simply cruxMirLogTag

mirLogMessageToSayWhat :: MirLogMessage -> SayWhat
mirLogMessageToSayWhat FinalResults = simply "---- FINAL RESULTS ----"
