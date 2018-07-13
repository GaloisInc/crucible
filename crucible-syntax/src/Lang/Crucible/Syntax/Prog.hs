module Lang.Crucible.Syntax.Prog where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.Exit
import Control.Monad.ST
import Control.Monad
import Text.Megaparsec as MP
import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.Atoms
import Lang.Crucible.CFG.SSAConversion

-- | The main loop body, useful for both the program and for testing.
go :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text -- ^ The contents of the input
   -> Bool -- ^ Whether to pretty-print the input data as well
   -> Handle -- ^ A handle that will receive the output
   -> IO ()
go fn theInput pprint outh =
  case MP.parse (many (sexp atom) <* eof) fn theInput of
    Left err ->
      do putStrLn $ parseErrorPretty' theInput err
         exitFailure
    Right v ->
      do when pprint $
           forM_ v $ T.hPutStrLn outh . printExpr
         cfgs <- stToIO $ top $ cfgs v
         case cfgs of
           Left err -> hPutStrLn outh $ show err
           Right ok ->
             forM_ ok $
              \(ACFG _ _ theCfg) ->
                hPutStr outh $ show (toSSA theCfg)
