module Main where

import Control.Exception (bracket)

import GHC.IO.Handle (hDuplicate, hDuplicateTo, hGetBuffering, hSetBuffering, Handle, BufferMode(..))

import System.Environment (withArgs)
import System.FilePath (takeBaseName, takeExtension, replaceExtension)
import System.IO --(IOMode(..), hFlush, withFile, stdout, stderr)

import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.HUnit (Assertion, testCaseSteps, assertBool, assertFailure)
import Test.Tasty.Golden (goldenVsFile, findByExtension)


import qualified CruxLLVMMain as C

main :: IO ()
main = defaultMain =<< suite

suite :: IO TestTree
suite =
  testGroup "crux-llvm" . pure <$> goldenTests "test-data/golden"


goldenTests :: FilePath -> IO TestTree
goldenTests dir =
  do cFiles <- findByExtension [".c"] dir
     return $
       testGroup "Golden testing of crux-llvm"
         [ goldenVsFile (takeBaseName cFile) goodFile outFile $
           withArgs [cFile] $
           withFile outFile WriteMode $
           C.mainWithOutputTo
         | cFile <- cFiles
         , notHidden cFile
         , let goodFile = replaceExtension cFile ".good"
         , let outFile = replaceExtension cFile ".out"
         ]
  where
    notHidden "" = True
    notHidden ('.' : _) = False
    notHidden _ = True

redir :: Handle -> [Handle] -> IO a -> IO a
redir _ [] act = act
redir out (h:hs) act =
  do hFlush h; hSetBuffering h NoBuffering; hSetBuffering out NoBuffering
     --buf <- hGetBuffering h
     let save =
           do old <- hDuplicate h
              hPutStrLn h "about to save"
              hFlush out; hFlush old
              hDuplicateTo out h
              hPutStrLn h "saved"
              return old
         restore old =
           do hFlush old; hFlush h
              hPutStrLn h "about to restore"
              hDuplicateTo old h
              hPutStrLn h "restored"
              --hSetBuffering h buf
     bracket save restore (const $ redir out hs act)
