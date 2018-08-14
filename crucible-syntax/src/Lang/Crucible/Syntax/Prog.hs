module Lang.Crucible.Syntax.Prog where

import Data.Text (Text)
--import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.Exit
import Control.Monad.ST
import Control.Monad
import Text.Megaparsec as MP

import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.ExprParse (printSyntaxError)
import Lang.Crucible.Syntax.Atoms


-- | The main loop body, useful for both the program and for testing.
go :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Bool     -- ^ Whether to pretty-print the input data as well
   -> Handle   -- ^ A handle that will receive the output
   -> IO ()
go fn theInput pprint outh =
  case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
    Left err ->
      do putStrLn $ parseErrorPretty' theInput err
         exitFailure
    Right v ->
      do when pprint $
           forM_ v $
             \e -> T.hPutStrLn outh (printExpr e) >> hPutStrLn outh ""
         cs <- stToIO $ top $ cfgs v
         case cs of
           Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
           Left err -> hPutStrLn outh $ show err
           Right ok ->
             forM_ ok $
              \(ACFG _ _ theCfg) ->
                do let ssa = toSSA theCfg
                   hPutStrLn outh $ show $ cfgHandle theCfg
                   hPutStrLn outh $ show ssa
