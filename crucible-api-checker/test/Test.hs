module Main where

import Control.Exception (bracket)

import GHC.IO.Handle (hDuplicate, hDuplicateTo, hSetBuffering, Handle, BufferMode(..))

import System.Environment (withArgs)
import System.FilePath (takeBaseName, replaceExtension)
import System.IO --(IOMode(..), hFlush, withFile, stdout, stderr)

import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.Golden (goldenVsFile, findByExtension)


import qualified CruxLLVMMain as C

main :: IO ()
main = defaultMain =<< suite

suite :: IO TestTree
suite =
  testGroup "crux-llvm" . pure <$> goldenTests "test-data/golden"


goldenTests :: FilePath -> IO TestTree
goldenTests dir =
  do cppFiles <- findByExtension [".cpp"] dir
     return $
       testGroup "Golden testing of crux-llvm"
         [ goldenVsFile (takeBaseName cppFile) goodFile outFile $
           withArgs ["--solver=z3",cppFile] $
           withFile outFile WriteMode $
           C.mainWithOutputTo
         | cppFile <- cppFiles
         , notHidden cppFile
         , let goodFile = replaceExtension cppFile ".good"
         , let outFile = replaceExtension cppFile ".out"
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
