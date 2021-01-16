{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Exception (bracket, SomeException, try)

import           GHC.IO.Handle (hDuplicate, hDuplicateTo)

import qualified Data.ByteString.Lazy as BSIO
import           Data.Char ( isLetter )
import           Data.List ( isInfixOf )
import           System.Directory ( doesFileExist )
import           System.Environment ( withArgs, lookupEnv )
import           System.Exit ( ExitCode(..) )
import           System.FilePath (takeBaseName, replaceExtension)
import           System.IO
import           System.Process ( readProcess )

import           Test.Tasty (defaultMain, testGroup, TestTree)
import           Test.Tasty.Golden (goldenVsString, findByExtension)

import qualified Crux.Log as C
import qualified CruxLLVMMain as C


main :: IO ()
main = do

  -- Determine which version of clang will be used for these tests.
  -- An exception (E.g. in the readProcess if clang is not found) will
  -- result in termination (test failure).  Uses partial 'head' but
  -- this is just tests, and failure is captured.
  clangBin <- lookupEnv "CLANG" >>= \case
    Just x -> return x
    Nothing -> return "clang"
  let isVerLine = isInfixOf "clang version"
      dropLetter = dropWhile (all isLetter)
      getVer = head . dropLetter . words . head . filter isVerLine . lines
  ver <- getVer <$> readProcess clangBin [ "--version" ] ""

  defaultMain =<< suite ver

suite :: String -> IO TestTree
suite clangVer =
  testGroup "crux-llvm" . pure . testGroup ("clang " <> clangVer) . pure <$> goldenTests "test-data/golden"


goldenTests :: FilePath -> IO TestTree
goldenTests dir =
  do cFiles <- findByExtension [".c",".ll"] dir
     return $
       testGroup "Golden testing of crux-llvm"
         [ goldenVsString (takeBaseName cFile) goodFile $
           do ex <- doesFileExist configFile
              let cfgargs = if ex then ["--config="++configFile] else []

              r <- withArgs (["--solver=z3",cFile] ++ cfgargs) $
                     withFile outFile WriteMode $ \h ->
                       let cfg = C.OutputConfig False h h True in -- Quiet mode, don't print colors
                       (let bss = BSIO.pack . fmap (toEnum . fromEnum) . show in \case
                         Left e -> "*** Crux failed with exception: " <> bss (show (e :: SomeException)) <> "\n"
                         Right (ExitFailure v) -> "*** Crux failed with non-zero result: " <> bss (show v) <> "\n"
                         Right ExitSuccess -> "")
                       <$>
                       (try $ C.mainWithOutputConfig cfg)
              (<> r) <$> BSIO.readFile outFile

         | cFile <- cFiles
         , notHidden cFile
         , let goodFile = replaceExtension cFile ".good"
         , let outFile = replaceExtension cFile ".out"
         , let configFile = replaceExtension cFile ".config"
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
