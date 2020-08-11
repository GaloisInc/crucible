{-# Language MultiWayIf #-}
{-# Language OverloadedStrings #-}
-- | Utilites for generating JSON
module Crux.UI.JS where

import Data.Text(unpack)
import Data.List(intercalate)
import Data.Maybe(fromMaybe)
import System.Directory( canonicalizePath )
import System.FilePath( isRelative )

import What4.ProgramLoc

jsLoc :: FilePath -> ProgramLoc -> IO JS
jsLoc cwd x =
  case plSourceLoc x of
    SourcePos f l c ->
      do let fstr = unpack f
         fabsolute <-
            if | null fstr -> pure ""
               | otherwise -> canonicalizePath fstr
         pure $ jsObj
           [ "file" ~> jsStr fabsolute
           , "line" ~> jsStr (show l)
           , "col"  ~> jsStr (show c)
           ]
    _ -> pure jsNull

--------------------------------------------------------------------------------
newtype JS = JS { renderJS :: String }

jsList :: [JS] -> JS
jsList xs = JS $ "[" ++ intercalate "," [ x | JS x <- xs ] ++ "]"

infix 1 ~>

(~>) :: a -> b -> (a,b)
(~>) = (,)

jsObj :: [(String,JS)] -> JS
jsObj xs =
  JS $ "{" ++ intercalate "," [ show x ++ ": " ++ v | (x,JS v) <- xs ] ++ "}"

jsBool :: Bool -> JS
jsBool b = JS (if b then "true" else "false")

jsStr :: String -> JS
jsStr = JS . show

jsNull :: JS
jsNull = JS "null"

jsMaybe :: Maybe JS -> JS
jsMaybe = fromMaybe jsNull

jsNum :: Show a => a -> JS
jsNum = JS . show


---------------------------------------------------

