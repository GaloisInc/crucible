module Main where

import Data.Monoid
import Data.SCargot
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Lang.Crucible.Syntax.Concrete

import qualified Options.Applicative as Opt

newtype TheFile = TheFile FilePath
  deriving (Eq, Show, Ord)


input :: Opt.Parser TheFile
input = TheFile <$> Opt.strArgument (Opt.metavar "FILE" <> Opt.help "The file to process")

data Options = Options { theFile :: TheFile
                       , replp :: Bool
                       }


--opts :: Opt.Parser Options
--opts = Options <$> Opt

main :: IO ()
main =
  do TheFile input <- Opt.execParser opts
     contents <- T.readFile input
     case decode parseExpr contents of
       Left err -> print err
       Right sexprs ->
         print sexprs

  where opts = Opt.info input (Opt.fullDesc)
