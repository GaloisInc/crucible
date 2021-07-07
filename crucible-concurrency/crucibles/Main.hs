{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
module Main where

import qualified Crux
import Cruces.CrucesMain
import Paths_crucible_concurrency (version)

main :: IO ()
main =
  Crux.withCruxLogMessage $
  Crux.loadOptions
    (Crux.defaultOutputConfig Crux.cruxLogMessageToSayWhat)
    "cruces" version cruciblesConfig
    $ run
