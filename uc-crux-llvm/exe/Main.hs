module Main (main) where

-- TODO RGS: Ugh. See https://gitlab.haskell.org/ghc/ghc/-/issues/19397.
import qualified RealMain (main)

main :: IO ()
main = RealMain.main
