{-# Language MultiWayIf #-}
{-# Language OverloadedStrings #-}
-- | Utilites for generating JSON
module Crux.UI.JS where

import Data.Text(unpack, Text)
import qualified Data.Text as Text
import Numeric
import Data.List(intercalate)
import Data.Maybe(fromMaybe)
import System.Directory( canonicalizePath )

import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson (decode, Value)
import qualified Data.ByteString.Lazy.Char8 as BL


import What4.ProgramLoc

jsLoc :: ProgramLoc -> IO (Maybe JS)
jsLoc x =
  case plSourceLoc x of
    SourcePos fname l c -> parsePos fname l c
    OtherPos s
      | fname : line : col : _rest <- Text.split (==':') s
      , (l,[]):_ <- readDec (Text.unpack (Text.strip line))
      , (c,[]):_ <- readDec (Text.unpack (Text.strip col)) ->
        parsePos fname l c
    _ -> pure Nothing
    where
    parsePos :: Text -> Int -> Int -> IO (Maybe JS)
    parsePos f l c = do
      let fstr = unpack f
      fabsolute <-
        if null fstr
          then pure ""
          else canonicalizePath fstr
      pure $ Just $ jsObj
        [ "file" ~> jsStr fabsolute
        , "line" ~> jsStr (show l)
        , "col"  ~> jsStr (show c)
        ]

--------------------------------------------------------------------------------
newtype JS = JS { renderJS :: String }

jsList :: [JS] -> JS
jsList xs = JS $ prettyPrintJson $ "[" ++ intercalate "," [ x | JS x <- xs ] ++ "]"

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



prettyPrintJson :: String -> String
prettyPrintJson s =
  case val of
    Just s' -> s'
    Nothing -> "Error parsing JSON!"
  where
  val = prettyPrintJson' s
  prettyPrintJson' :: String -> Maybe String
  prettyPrintJson' str = do
    val' <- decode (BL.pack str) :: Maybe Value
    pure $ BL.unpack (encodePretty val')

---------------------------------------------------

