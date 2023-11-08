{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
module Main (main) where

import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.IO

import Lang.Crucible.Syntax.Concrete (defaultParserHooks)
import Lang.Crucible.Syntax.ExprParse
import Lang.Crucible.Syntax.Prog (doParseCheck)
import Lang.Crucible.Syntax.SExpr

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden
import Test.Tasty.HUnit
import qualified Text.Megaparsec as MP
import System.FilePath
import System.Directory

import What4.ProgramLoc (Position(SourcePos), Posd(..))

main :: IO ()
main = do wd <- getCurrentDirectory
          putStrLn $ "Looking for tests in " ++ wd
          parseTests <- findTests "Parsing round-trips" "test-data" testParser
          let allTests = testGroup "Tests" [syntaxParsing, parseTests]
          defaultMain allTests

findTests :: String -> FilePath -> (FilePath -> FilePath -> IO ()) -> IO TestTree
findTests group_name test_dir test_action =
  do inputs <- findByExtension [".cbl"] test_dir
     return $ testGroup group_name
       [ goldenFileTestCase input test_action
       | input <- List.sort inputs
       ]

goldenFileTestCase :: FilePath -> (FilePath -> FilePath -> IO ()) -> TestTree
goldenFileTestCase input test_action =
  goldenVsFileDiff
   (takeBaseName input) -- test name
   (\x y -> ["diff", "-u", x, y])
   goodFile -- golden file path
   outFile
   (test_action input outFile) -- action whose result is tested
  where
    outFile = replaceExtension input ".out"
    goodFile = replaceExtension input ".out.good"

testParser :: FilePath -> FilePath -> IO ()
testParser inFile outFile =
  do contents <- T.readFile inFile
     let ?parserHooks = defaultParserHooks
     withFile outFile WriteMode $ doParseCheck inFile contents True

data Lam = Lam [Text] (Datum TrivialAtom) deriving (Eq, Show)

syntaxParsing :: TestTree
syntaxParsing =
  let
    anyUnit :: SyntaxParse TrivialAtom ()
    anyUnit = anything *> pure ()
    vars :: SyntaxParse TrivialAtom [TrivialAtom]
    vars = describe "sequence of variable bindings" $ rep atomic
    distinctVars :: SyntaxParse TrivialAtom [TrivialAtom]
    distinctVars = sideCondition' "sequence of distinct variable bindings" (\xs -> List.nub xs == xs) vars
    lambda =
      fmap (\(_, (xs, (body, ()))) -> Lam [x | TrivialAtom x <- xs] (syntaxToDatum body))
      (cons (atom "lambda") $
       cons distinctVars $
       cons anything $ emptyList)
  in testGroup "Syntax parsing lib"
       [ testCase "Empty list is empty list" $
         do x <- syntaxTest "()" emptyList
            x @?= Right ()
       , testCase "Empty list is not atom" $
         do x <- syntaxTest "()" (atom ("foo" :: TrivialAtom))
            x @?= Left
             (SyntaxError $ pure $
               Reason { expr = Syntax {unSyntax = Posd {pos = fakeFilePos 1 1, pos_val = List []}}
                        , message = "foo"
                        })
       , testCase "Atom is not empty list" $
          do x <- syntaxTest "foo" emptyList
             x @?= Left
               (SyntaxError $ pure $
                 Reason { expr = Syntax {unSyntax = Posd {pos = fakeFilePos 1 1, pos_val = Atom (TrivialAtom "foo")}}
                          , message = "empty expression ()"
                          })
       , testCase "Three element list of whatever" $
         do x <- syntaxTest "(delicious avocado toast)" (list [anyUnit, anyUnit, anyUnit])
            x @?= Right [(), (), ()]
       , testCase "Three element list of whatever, again" $
         do x <- syntaxTest "(delicious (avocado and tomato) toast)" (list [anyUnit, anyUnit, anyUnit])
            x @?= Right [(), (), ()]
       , testCase "Three element list of atoms" $
         do x <- syntaxTest "(delicious avocado toast)" (list [atomic, atomic, atomic])
            x @?= Right [TrivialAtom "delicious", TrivialAtom "avocado", TrivialAtom "toast"]
       , testCase "Three element list of non-atoms isn't atoms" $
         do x <- syntaxTest "((delicious) avocado toast)" (list [atomic, atomic, atomic])
            x @?= Left
               (SyntaxError $ pure $
                 Reason { expr =
                            Syntax $
                            Posd { pos = fakeFilePos 1 2
                                 , pos_val =
                                     List [ Syntax (Posd (fakeFilePos 1 3)
                                                     (Atom (TrivialAtom "delicious")))
                                          ]
                                 }
                        , message = "an atom"
                        })
       , testCase "Three element list of non-atoms still isn't atoms" $
         do x <- syntaxTest "(delicious (avocado) toast)" (list [atomic, atomic, atomic])
            x @?= Left
               (SyntaxError $ pure $
                 Reason { expr =
                            Syntax $
                              Posd { pos = fakeFilePos 1 12
                                   , pos_val =
                                       List [ Syntax (Posd (fakeFilePos 1 13)
                                                        (Atom (TrivialAtom "avocado")))
                                            ]
                                   }
                          , message = "an atom"
                          })
       , testCase "Many three-element lists of whatever (1)" $
         do x <- syntaxTest "((delicious avocado toast))" (rep $ list [anything, anything, anything] *> pure ())
            x @?= Right [()]
       , testCase "Many three-element lists of whatever (0)" $
         do x <- syntaxTest "()" (rep $ list [anything, anything, anything] *> pure ())
            x @?= Right []
       , testCase "Many three-element lists of whatever (4)" $
         do x <- syntaxTest "((programming is fun) (a b c) (x y z) (hello (more stuff) fits))" (rep $ list [anything, anything, anything] *> pure ())
            x @?= Right [(), (), (), ()]
       , testCase "Many three-element lists of whatever failing on third sublist" $
         do x <- syntaxTest "((programming is fun) (a b c) (x y) (hello (more stuff) fits))" (rep $ list [anything, anything, anything] *> pure ())
            x @?= Left
               (SyntaxError $ pure $
                Reason { expr = Syntax (Posd (fakeFilePos 1 31)
                                         (List [ Syntax (Posd (fakeFilePos 1 32)
                                                          (Atom (TrivialAtom "x")))
                                               , Syntax (Posd (fakeFilePos 1 34)
                                                          (Atom (TrivialAtom "y")))]))
                       , message = "3 expressions"
                       })
       , testCase "Realistic example 1" $
         do x <- syntaxTest "(lambda (x y z) y)" lambda
            x @?= Right (Lam ["x", "y", "z"] (Datum (Atom "y")))
       , testCase "Realistic example 2" $
         do x <- syntaxTest "(lambda (x y (z)) y)" lambda
            x @?= Left
                (SyntaxError $ pure $
                 Reason { expr = Syntax (Posd (fakeFilePos 1 14)
                                            (List [Syntax {unSyntax = Posd {pos = fakeFilePos 1 15, pos_val = Atom (TrivialAtom "z")}}]))
                          , message = "an atom"
                          })
       , testCase "Realistic example 3" $
         do x <- syntaxTest "(lambda x x)" lambda
            x @?= Left
                (SyntaxError $ pure $
                 Reason { expr = Syntax (Posd (fakeFilePos 1 9)
                                            (Atom "x"))
                          , message = "sequence of variable bindings"
                          })
       , testCase "Realistic example 4" $
         do x <- syntaxTest "(lambda (x y x) y)" lambda
            x @?= Left
                (SyntaxError $ pure $
                 Reason { expr =
                            Syntax (Posd (fakeFilePos 1 9)
                                     (List [ Syntax {unSyntax = Posd {pos = fakeFilePos 1 10, pos_val = Atom (TrivialAtom "x")}}
                                           , Syntax {unSyntax = Posd {pos = fakeFilePos 1 12, pos_val = Atom (TrivialAtom "y")}}
                                           , Syntax {unSyntax = Posd {pos = fakeFilePos 1 14, pos_val = Atom (TrivialAtom "x")}}
                                           ]))
                          , message = "sequence of distinct variable bindings"
                          })
       ]

fakeFile :: Text
fakeFile = "test input"

fakeFilePos :: Int -> Int -> Position
fakeFilePos = SourcePos fakeFile

syntaxTest :: Text -> SyntaxParse TrivialAtom a -> IO (Either (SyntaxError TrivialAtom) a)
syntaxTest txt p =
  case MP.parse (skipWhitespace *> sexp (TrivialAtom <$> identifier) <* MP.eof) (T.unpack fakeFile) txt of
     Left err -> error $ "Reader error: " ++ MP.errorBundlePretty err
     Right sexpr -> syntaxParseIO p sexpr

