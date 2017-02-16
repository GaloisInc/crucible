module Main (main) where

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Solver.SimpleBackend
import           Lang.Crucible.Solver.Symbol
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.SimpleBackend.Acirc
import           Data.Parameterized.Nonce


main :: IO ()
main = do
  putStrLn "crucible2acirc version 0.1.0"
  withIONonceGenerator $ \gen -> do
    sym <- newSimpleBackend gen
    stopCaching sym
    -- Example
    _0 <- freshConstant sym (systemSymbol "x0!") BaseIntegerRepr
    _1 <- freshConstant sym (systemSymbol "y1!") BaseIntegerRepr
    _2 <- freshConstant sym (systemSymbol "z2!") BaseIntegerRepr

    _3 <- intAdd sym _2 _1
    _4 <- intMul sym _1 _0
    _5 <- intMul sym _4 _3
    _6 <- intAdd sym _3 _5
    print (printSymExpr _6)
    generateCircuit "test-mul.acirc" [_6]
