{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiWayIf #-}

module TestUtils where

import           Control.Monad ( when )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Parameterized.Classes
import           Data.Parameterized.TraversableFC
import           Hedgehog
import           System.Directory
import qualified What4.Expr.Builder as S
import qualified What4.Interface as WI

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



symFnEqualityTest :: ( MonadIO m
                     , MonadTest m
                     , sym ~ S.ExprBuilder t st flgs
                     ) =>
                     sym
                  -> WI.SymFn sym args ret
                  -> WI.SymFn sym arts' ret'
                  -> m ()
symFnEqualityTest sym fn1 fn2 =
  let
    argTypes1 = WI.fnArgTypes fn1
    argTypes2 = WI.fnArgTypes fn2
    retType1 = WI.fnReturnType fn1
    retType2 = WI.fnReturnType fn2
  in if | Just Refl <- testEquality argTypes1 argTypes2
        , Just Refl <- testEquality retType1 retType2
        , S.ExprSymFn _ _ (S.DefinedFnInfo argBVs1 efn1 _) _ <- fn1
        , S.ExprSymFn _ _ (S.DefinedFnInfo argBVs2 efn2 _) _ <- fn2 -> do
          args <- traverseFC (\bv -> liftIO $ WI.freshConstant sym (S.bvarName bv) (S.bvarType bv)) argBVs1
          expr1 <- liftIO $ S.evalBoundVars sym efn1 argBVs1 args
          expr2 <- liftIO $ S.evalBoundVars sym efn2 argBVs2 args
          case testEquality expr1 expr2 of
            Just Refl -> success
            Nothing -> do
              debugOut $ "Resulting expressions do not match:\n"
                ++ "fn1:\n" ++ (show expr1) ++ "\n"
                ++ "fn2:\n" ++ (show expr2)
              failure
        | otherwise -> do
            debugOut $ "Mismatch in function signatures: "
              ++ "fn1: " ++ show argTypes1 ++ "\n" ++ show retType1 ++ "\n"
              ++ "fn2: " ++ show argTypes2 ++ "\n" ++ show retType2
            failure