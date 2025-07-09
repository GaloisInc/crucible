{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>

This test suite is composed of golden test files.
Each file consists of inputs (@Statement@s) that begin with @> @, and outputs that follow them.
This comingling of inputs and outputs stands in contrast to a more customary golden test setup where the inputs are in one file and the outputs in another.
It makes the relationship between various inputs and outputs clear at a glance, which makes the tests easier to read and understand in a text editor or web interface.
This readability comes at the cost of a mildly gnarly test harness (see, e.g., 'parseTest' and 'runScript').
To create a new test, simply create a new file with all of the input lines, and then run the test suite with the @--accept@ flag, i.e., @cabal test -- --accept@.
-}

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main (main) where

import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as BS
import Data.IORef qualified as IORef
import Data.List qualified as List
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding as Text
import Data.Text.IO as IO
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.Debug.Inputs qualified as Inps
import Lang.Crucible.Debug.Outputs qualified as Outps
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text qualified as PP
import System.Directory qualified as Dir
import Test.Tasty qualified as Tasty
import Test.Tasty.Golden qualified as Golden

testDir :: FilePath
testDir = "test-data/"

-- | Parse a test file into a sequence of inputs and outputs
parseTest :: Text -> [(Text, Text)]
parseTest txt = List.reverse (go [] Nothing (Text.lines txt))
  where
    go ::
      -- | Accumulated result
      [(Text, Text)] ->
      -- | Perhaps (input, accumulated output)
      Maybe (Text, [Text]) ->
      -- | Remaining lines
      [Text] ->
      [(Text, Text)]
    go accum Nothing [] = accum
    go accum (Just (inp, out)) [] = (inp, Text.unlines (List.reverse out)) : accum
    go accum soFar (l:ls) =
      if l == ""
      then go accum soFar ls
      else
        case (soFar, Text.stripPrefix "> " l) of
          (Nothing, Nothing) -> error "Ill-formed test file"
          (Nothing, Just l') -> go accum (Just (l', [])) ls
          (Just (inp, out), Nothing) -> go accum (Just (inp, l:out)) ls
          (Just (inp, out), Just l') ->
            let accum' = (inp, Text.unlines (List.reverse out)) : accum in
            go accum' (Just (l', [])) ls

runScript :: FilePath -> IO ByteString
runScript path = do
  testTxt <- IO.readFile path
  let parsed = parseTest testTxt
  let inputTxtLines = map fst parsed ++ ["done"]
  inps <- Inps.parseInputs Debug.voidExts <$> Inps.prepend inputTxtLines Inps.fail
  r <- IORef.newIORef []
  let logger = \_ -> pure ()
  Debug.bareDebugger inps (Outps.accumulate r) logger
  outs <- List.reverse <$> IORef.readIORef r
  let outsTxt = map (PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions . PP.pretty) outs
  let inOuts = zipWith (\i o -> "> " <> i <> "\n\n" <> o <> "\n") inputTxtLines outsTxt
  pure (Text.encodeUtf8 (Text.unlines inOuts))

mkTest :: FilePath -> FilePath -> Tasty.TestTree
mkTest dir path =
  Golden.goldenVsStringDiff
  path
  (\x y -> ["diff", "-u", x, y])
  (dir ++ path)
  (BS.fromStrict <$> runScript (dir ++ path))

loadTests :: FilePath -> IO Tasty.TestTree
loadTests dir = do
  -- This `List.sort` is not technically necessary, it just ensures that test
  -- cases will be performed in a stable ordering, since `Dir.listDirectory`
  -- doesn't guarantee such an ordering.
  files <- List.sort <$> Dir.listDirectory dir
  let dbgScripts = List.filter (".txt" `List.isSuffixOf`) files
  let tests = map (uncurry mkTest) (map (dir,) dbgScripts)
  pure (Tasty.testGroup dir tests)

main :: IO ()
main = do
  mainTests <- loadTests testDir
  completeTests <- loadTests (testDir ++ "complete/")
  errorTests <- loadTests (testDir ++ "error/")
  styleTests <- loadTests (testDir ++ "style/")
  let tests = [mainTests, completeTests, errorTests, styleTests]
  Tasty.defaultMain (Tasty.testGroup "Tests" tests)
