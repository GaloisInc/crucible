{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


module Mir.DefId where

--import qualified Data.List as List
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

     core/ae3efe0::option[0]::Option[0]::None[0]

     ::option[0]::{{impl}}[0]::unwrap_or_else[0]

     core/ae3efe0::ops[0]::function[0]::FnOnce[0]::call_once[0]

     ::Lmcp[0]::ser[0]

     ::f[0]


This module parses these names to help with identifying and extracting
the underlying structure.

For example, the 'None' data constructor is defined in the std library
file, as part of the 'option' module, and the 'Option' ADT.

     core/ae3efe0::option[0]::Option[0]::None[0]

     ^^^^^^^^^^^^  ^^^^^^^^^  ^^^^^^^^^  ^^^^^^^
        file         path       name      extra

The filename can be omitted for local declarations. After the
filename, each part includes a numeric annotation (the '[0]') for
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

      core/ae3efe0::option[0]::Option[0]::None[0]

      ret/8cd878b::E[0]::A[0]::0[0]

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

-- | if True, suppress the source file when pretty-printing MIR identifiers.
hideSourceFile :: Bool
hideSourceFile = False

-- | if True, suppress the [0] annotations when pretty-printing MIR identifiers.
hideEntrySyms :: Bool
hideEntrySyms = False

-----------------------------------------------


-- | The module name for the rust core library used by mir-json.
-- If mir-json changes, we will need to update this name.
stdlib :: Text
stdlib = pack "core/ae3efe0"

type Entry = (Text,Int)
-- | Identifiers that can be qualified by paths
data DefId = DefId { did_file     :: Text    -- ^ e.g. core/ae3efe0    
                   , did_path     :: [Entry] -- ^ e.g. ::ops[0]::function[0] 
                   , did_name     ::  Entry  -- ^ e.g. 
                                         --        ::T[0]          -- Trait name
                                         --        ::Option[0]     -- ADT type
                                         --        ::f[0]          -- function name, must be last
                   , did_extra    :: [Entry] -- ^ e.g. ::Some[0]       -- variant name
                                         --        ::Some[0]::0    -- field
                   }
  deriving (Eq, Ord, Generic)


isImpl :: DefId -> Bool
isImpl defid =
  not (null (did_path defid)) &&
  fst (last (did_path defid)) == "{{impl}}"

-- | If we have a static call for a trait, we need to mangle the format so that it looks
-- like a normal function call (and we can find the function handle)
mangleTraitId :: DefId -> DefId
mangleTraitId d@(DefId file path _name extra)
  | not (null extra) = DefId file (path ++ [("{{impl}}", 0)]) (head extra) (tail extra)
  | otherwise        = d

-- | If we have a static call for a trait, we need to mangle the format so that it looks
-- like a normal function call (and we can find the function handle)
makeImpl0 :: DefId -> DefId
makeImpl0 (DefId file path name extra) =
  DefId file (changeImpl path) name extra where
     changeImpl p | not (null p) && fst (last p) == ("{{impl}}"::Text) = init p ++ [("{{impl}}",0)]
                  | otherwise = p



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

-- | Detect a defid is in an {{impl}} and pull out the method name.
-- 
parseImplName :: DefId -> Maybe Entry
parseImplName (DefId _ path@(_:_) name _)
  | fst (last path) == "{{impl}}" = Just name
parseImplName _ = Nothing


-- | Is this entry the same as the method name?
-- NOTE: trait methods have the Trait as the name, and the specific
-- method afterwards
sameTraitMethod :: Entry -> DefId -> Bool
sameTraitMethod meth1 (DefId _ _ _ (meth2:_)) = meth1 == meth2
sameTraitMethod _     (DefId _ _ _ []) = False


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
       
showEntry :: Entry -> Text
showEntry (txt,n) = pack (unpack txt ++ "[" ++ (show n) ++ "]")

-- lowercase identifiers or {{impl}}
-- the regex is more permissive than this...
isPath :: String -> Bool
isPath str = isJust (Regex.matchRegex (Regex.mkRegex ( "^[{a-z]+[{}A-Za-z0-9_]*"))  str)

           
-- | Parse text from mir-json to produce a DefId       
textId :: Text -> DefId
textId txt = case splitInput (unpack txt) of
  (hd : rest ) -> let (fl, entries) = case parseEntry hd of
                        Nothing -> (hd, catMaybes $ map parseEntry rest)
                        Just entry -> ("", entry: (catMaybes $ map parseEntry rest))
                      pack2 (x,y) = (pack x, y)
                  in case span (isPath . fst) entries of
                       ([], [])     -> error $ "cannot parse id " ++ unpack txt
                       ([], y:ys)   -> DefId (pack fl) [] (pack2 y) (map pack2 ys)
                       (xs, [])     -> DefId (pack fl) (map pack2 (init xs)) (pack2 (last xs)) []
                       (xs, y : ys) -> DefId (pack fl) (map pack2 xs)        (pack2 y)  (map pack2 ys)
                    
  [] -> error "empty text for DefId"
                  
       

idText :: DefId -> Text
idText (DefId fl mods nm ex) =
  intercalate "::" (fl : map showEntry (mods++nm:ex))

-- ignores filename and entry #s
instance Pretty DefId where
  pretty (DefId fl mods nm ex) =
    let ppEntry = if hideEntrySyms  then fst else showEntry
        addmods = if hideModuleName then id else (mods++)
        addfl   = if hideSourceFile then id else (fl:)
    in
{-    text (unpack fl) <> braces (text $ unpack $ intercalate "::" (map ppEntry mods))
                     <> text (unpack (ppEntry nm))
            <> braces (text $ unpack $  intercalate "::" (map ppEntry ex)) -}
    text $ unpack $ intercalate "::" (addfl (map ppEntry  (addmods (nm:ex))))

instance Show DefId where
  show defId = unpack (idText defId)
instance IsString DefId where
  fromString str = textId (fromString str)
instance FromJSON DefId where
    parseJSON x = textId <$> parseJSON x

relocateDefId :: DefId -> DefId
relocateDefId (DefId _did_file pth nm ex) = DefId stdlib pth nm ex


--- Custom stuff
--

-- Custom function calls are converted by hand. The below can probably do away with regex and use [0], but I'm not sure if that would always work

{-
matchCustomFunc :: Text -> Maybe Text
matchCustomFunc fname1
  | Just _ <- Regex.matchRegex (Regex.mkRegex "::boxed\\[[0-9]+\\]::\\{\\{impl\\}\\}\\[[0-9]+\\]::new\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "boxnew"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::slice\\[[0-9]+\\]::\\{\\{impl\\}\\}\\[[0-9]+\\]::into_vec\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "slice_tovec"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::vec\\[[0-9]+\\]::\\{\\{impl\\}\\}\\[[0-9]+\\]::as_mut_slice\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "vec_asmutslice"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::ops\\[[0-9]+\\]::index\\[[0-9]+\\]::Index\\[[0-9]+\\]::index\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "index"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::vec\\[[0-9]+\\]::from_elem\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "vec_fromelem"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::ops\\[[0-9]+\\]::function\\[[0-9]+\\]::Fn\\[[0-9]+\\]::call\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "call"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::iter\\[[0-9]+\\]::traits\\[[0-9]+\\]::IntoIterator\\[[0-9]+\\]::into_iter\\[[0-9]+\\]") (unpack (idText fname1))
    = trace "isCustomFunc: into_iter" $ Just "into_iter"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::iter\\[[0-9]+\\]::iterator\\[[0-9]+\\]::Iterator\\[[0-9]+\\]::next\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "iter_next"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::iter\\[[0-9]+\\]::iterator\\[[0-9]+\\]::Iterator\\[[0-9]+\\]::map\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "iter_map"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::iter\\[[0-9]+\\]::iterator\\[[0-9]+\\]::Iterator\\[[0-9]+\\]::collect\\[[0-9]+\\]") (unpack (idText fname1))
    = Just "iter_collect"

  -- TODO into_vec
  --    (vec, 0) -> vec
  -- TODO Iterator::map
  --    ((vec,0), closure) -> (closure of vec, 0)
  -- TODO Iterator::collect
  --    (vec, 0) -> vec

  | otherwise = Nothing
-}

isCustomFunc :: DefId -> Maybe Text
isCustomFunc defid = case (did_path defid, did_name defid, did_extra defid) of
  
   ([("boxed", _),("{{impl}}",_)], ("new",_), [])            -> Just "new"
   
   ([("slice", _),("{{impl}}",_)], ("slice_tovec",_), [])    -> Just "slice_tovec"
   ([("slice", _),("{{impl}}",_)], ("len",_), [])            -> Just "slice_len"
   ([("slice", _),("{{impl}}",_)], ("get_unchecked",_), [])     -> Just "slice_get"
   ([("slice", _),("{{impl}}",_)], ("get_unchecked_mut",_),[])  -> Just "slice_get_mut"

   -- these are trait implementations
   ([("ops", _), ("index",_)], ("Index", _), [("index",_)])     -> Just "index"
   ([("ops", _), ("index",_)], ("IndexMut", _), [("index_mut",_)]) -> Just "index_mut"

   ([("vec", _), ("{{impl}}",_)], ("vec_asmutslice",_),[])   -> Just "vec_asmutslice"
   
   ([("ops",_),("function",_)], ("Fn", _), [("call", _)])            -> Just "call"
   ([("ops",_),("function",_)], ("FnOnce", _), [("call_once", _)])   -> Just "call"

   ([("process",_)], ("exit",_), []) -> Just "exit"
   -- TODO add more
   _ -> Nothing


