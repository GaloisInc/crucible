{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}

module TestUtils where

import           Control.Monad ( when )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Parameterized.Classes
import           Data.Parameterized.TraversableFC
import           Hedgehog
import           System.Directory
import qualified What4.Expr.Builder as S
import qualified What4.Interface as WI
import qualified What4.Serialize.Normalize as WN

import           Prelude


debugFile :: FilePath
debugFile = "what4serialize.log"

debugReset :: IO ()
debugReset = do e <- doesFileExist debugFile
                when e $ removeFile debugFile

debugOut, alwaysPrint :: MonadIO m => String -> m ()
debugOut msg = liftIO $ do appendFile debugFile (msg <> "\n")
                           -- alwaysPrint  -- comment this out to disable printing
                           return ()
alwaysPrint = liftIO . putStrLn


showSymFn :: S.ExprSymFn t args ret -> String
showSymFn fn = case S.symFnInfo fn of
  S.DefinedFnInfo _ expr _ -> (show $ WI.printSymExpr expr)
  _ -> ""

symFnEqualityTest :: ( MonadIO m
                     , MonadTest m
                     , sym ~ S.ExprBuilder t st flgs
                     ) =>
                     sym
                  -> WI.SymFn sym args ret
                  -> WI.SymFn sym arts' ret'
                  -> m ()
symFnEqualityTest sym fn1 fn2 = do
  (liftIO $ WN.testEquivSymFn sym fn1 fn2) >>= \case
    WN.ExprEquivalent -> success
    WN.ExprNormEquivalent -> success
    WN.ExprUnequal -> do
      debugOut $ "Resulting functions do not match:\n"
        ++ "fn1:\n" ++ (showSymFn fn1) ++ "\n"
        ++ "fn2:\n" ++ (showSymFn fn2)
      failure
