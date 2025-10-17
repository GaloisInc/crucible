{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
module Main (main) where

import qualified Crux
import Cruces.CrucesMain
import Paths_crucible_concurrency (version)

main :: IO ()
main = do
  mkOutCfg <- Crux.defaultOutputConfig Crux.cruxLogMessageToSayWhat
  Crux.withCruxLogMessage $
    Crux.loadOptions mkOutCfg "cruces" version cruciblesConfig
    $ run
