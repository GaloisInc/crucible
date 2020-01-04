{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


module Mir.DefId
( DefId
, textId
, idText
, ExplodedDefId
, idKey

, getTraitName
, cleanVariantName
, parseFieldName
) where

import Data.Aeson

import Data.Text (Text, pack, unpack, intercalate)
import qualified Text.Regex as Regex

import Data.Maybe (catMaybes, isJust)

import Data.String (IsString(..))
import GHC.Generics

import qualified Debug.Trace as Debug

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

-----------------------------------------------
{-

 A DefId, when produced by mir-json, looks something like

     ::option[0]::Option[0]::None[0]

     ::option[0]::{{impl}}[0]::unwrap_or_else[0]

     ::ops[0]::function[0]::FnOnce[0]::call_once[0]

     ::Lmcp[0]::ser[0]

     ::f[0]


This module parses these names to help with identifying and extracting
the underlying structure.

For example, the 'None' data constructor is defined in the std library
file, as part of the 'option' crate, and the 'Option' ADT.

     ::option[0]::Option[0]::None[0]

     ^^^^^^^^^  ^^^^^^^^^  ^^^^^^^
       path       name      extra

Each part includes a numeric annotation (the '[0]') for
disambiguation. Most of the time, the names are unique within a file
so the number is [0]. However, Rust definitions may be overloaded, and
this number resolves that overloading at the Mir level.

The module *path* may be empty (for local definitions) or may include
nested modules (e.g. ::ops[0]::function[0]::FnOnce[0]). It may also
include {{impl}}[0] and nested functions
(e.g. ::{{impl}}[0]::ser[0]::{{closure}}, the anonymous function
defined within another function.)

The *name* is the first component of the defid that is not part of the
module path. Anything after the name is part of *extra*.

The name could be:

  - a function name

      ::f[0]

      ::{{impl}}[0]::ser[0]

      (extra will be nil)

  - an ADT name

      ::option[0]::Option[0]::None[0]

      ::E[0]::A[0]::0[0]

      (extra, if non-nil indicates a variant, and then a field within that variant)

  - a trait name

      ::Lmcp[0]::ser[0]

      (extra, if non-nil, contains the trait function)


  - {{closure}}

      ::{{impl}}[0]::ser[0]::{{closure}}


-}



-----------------------------------------------
-- These flags only control the behavior of 'pretty' for DefIds.
-- The idText function always produces the full text of the DefId.

-- TODO: make command-line options for PP

-- | if True, suppress the module name when pretty-printing MIR identifiers.
hideModuleName :: Bool
hideModuleName = False

-- | if True, suppress the [0] annotations when pretty-printing MIR identifiers.
hideEntrySyms :: Bool
hideEntrySyms = False

-----------------------------------------------


type Entry = (Text,Int)
-- | Identifiers that can be qualified by paths
data DefId = DefId { 
                     did_path     :: [Entry] -- ^ e.g. ::ops[0]::function[0] 
                   , did_name     ::  Entry  -- ^ e.g. 
                                         --        ::T[0]          -- Trait name
                                         --        ::Option[0]     -- ADT type
                                         --        ::f[0]          -- function name, must be last
                   , did_extra    :: [Entry] -- ^ e.g. ::Some[0]   -- variant name
                                         --        ::Some[0]::0    -- field
                   }
  deriving (Eq, Ord, Generic)

-- If a DefId is the name of a *static* method, we can find a trait name inside of it
-- by removing the "extra" part
getTraitName :: DefId -> DefId
getTraitName (DefId p n _e) = (DefId p n [])




-- | Find the variant name and return it, without any decoration
cleanVariantName :: DefId -> Text
cleanVariantName defid = case did_extra defid of
   (varName, _):_ -> varName
   _              -> fst (did_name defid)

-- | Find the field anem and return it, without any decoration
-- ret/8cd878b::E[0]::A[0]::0[0]  ==> 0
-- ret/8cd878b::S[0]::x[0]        ==> x
parseFieldName :: DefId -> Maybe Text
parseFieldName defid = case (did_extra defid) of
  [( x, _n )]      -> Just x
  [ _ , (num, _m)] -> Just num
  _ -> Nothing



--  divide the input into components separated by double colons
splitInput :: String -> [String]
splitInput str = go str [ "" ] where
    go [] strs                 = reverse (map reverse strs)
    go (':' : ':' : rest) strs = go rest ([]:strs)
    go (a : rest) (hd:strs)    = go rest ((a:hd):strs)
          

--  recognize a string followed by a bracketed number
parseEntry :: String -> Maybe (String, Int)
parseEntry str = case Regex.matchRegex (Regex.mkRegex ( "^([{}A-Za-z0-9_]+)" ++ "\\[([0-9]+)\\]$")) str of
                  Just [idn, num] -> Just (idn, read num)
                  Nothing        -> Nothing

-- leave off [0], only add it for nonzero defid's       
showEntry :: Entry -> Text
showEntry (txt,n) = pack (unpack txt ++ "[" ++ (show n) ++ "]")

-- lowercase identifiers or {{impl}}
-- the regex is more permissive than this...
isPath :: String -> Bool
isPath str = isJust (Regex.matchRegex (Regex.mkRegex ( "^[{a-z]+[{}A-Za-z0-9_]*"))  str)

           
-- | Parse text from mir-json to produce a DefId       
textId :: Text -> DefId
textId txt = case splitInput (unpack txt) of
  (hd : rest ) -> let (_fl, entries) = case parseEntry hd of
                        Nothing -> (hd, catMaybes $ map parseEntry rest)
                        Just entry -> ("", entry: (catMaybes $ map parseEntry rest))
                      pack2 (x,y) = (pack x, y)
                  in case span (isPath . fst) entries of
                       ([], [])     -> error $ "cannot parse id " ++ unpack txt
                       ([], y:ys)   -> DefId [] (pack2 y) (map pack2 ys)
                       (xs, [])     -> DefId (map pack2 (init xs)) (pack2 (last xs)) []
                       (xs, y : ys) -> DefId (map pack2 xs)        (pack2 y)  (map pack2 ys)
                    
  [] -> error "empty text for DefId"
                  
       
-- | Extract the text from a DefId
idText :: DefId -> Text
idText (DefId mods nm ex) =
  intercalate "::" ("" : map showEntry (mods++nm:ex))

type ExplodedDefId = ([Text], Text, [Text])
idKey :: DefId -> ExplodedDefId
idKey did =
    ( map fst (did_path did)
    , fst (did_name did)
    , map fst (did_extra did)
    )

-- ignores filename and entry #s
instance Pretty DefId where
  pretty (DefId mods nm ex) =
    let ppEntry (txt, n) = if hideEntrySyms  then txt else if n == 0 then txt else showEntry (txt,n)
        addmods = if hideModuleName then id else (mods++)
    in
    text $ unpack $ intercalate "::" (map ppEntry  (addmods (nm:ex)))

  


instance Show DefId where
  show defId = unpack (idText defId)
instance IsString DefId where
  fromString str = textId (fromString str)
instance FromJSON DefId where
    parseJSON x = textId <$> parseJSON x





