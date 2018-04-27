{-# Language TemplateHaskell #-}
module CLibSrc where

import Language.Haskell.TH(Q,Dec,runIO)
import Language.Haskell.TH.Syntax(addDependentFile)
import System.Directory(makeAbsolute)

cLibSrc :: Q [Dec]
cLibSrc = do let path = "c-src/sv-comp.c"
             absPath <- runIO (makeAbsolute path)
             addDependentFile absPath
             c_lib <- runIO (readFile absPath)
             [d| c_src :: String; c_src = c_lib |]


