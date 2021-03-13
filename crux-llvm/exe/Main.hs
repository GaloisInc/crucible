{- | This is the main executable for running the Crux LLVM verification
   on LLVM BitCode objects that can be built from C and C++ sources
   using Clang and llvm-link. -}

module Main (main) where
-- TODO RGS: Ugh. See https://gitlab.haskell.org/ghc/ghc/-/issues/19397.
import qualified RealMain (main)

main :: IO ()
main = RealMain.main
