{-# LANGUAGE ImplicitParams #-}
module Main ( main ) where

import qualified Test.Tasty as T
import qualified Control.Exception as CE

import qualified What4.Utils.Util as U
import qualified What4.Utils.Log as U
import           SymFnTests


allTests :: (U.HasLogCfg) => T.TestTree
allTests = T.testGroup "What4" symFnTests

main :: IO ()
main = do
  logCfg <- U.mkLogCfg "main"
  let ?logCfg = logCfg
  U.withAsyncLinked (U.tmpFileLogEventConsumer (const True) logCfg) $
    const $ T.defaultMain allTests `CE.finally` U.logEndWith logCfg
