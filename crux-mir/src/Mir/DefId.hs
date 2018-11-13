{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


module Mir.DefId where

--import qualified Data.List as List
import Data.Text (Text, pack, unpack, intercalate)
import qualified Text.Regex as Regex

import Data.Maybe (catMaybes, isJust)

import Data.String (IsString(..))
import GHC.Generics

import Debug.Trace




-- | The module name for the rust core library used by mir-json.
-- If mir-json changes, we will need to update this name.
stdlib :: Text
stdlib = pack "core/ae3efe0"

type Entry = (Text,Int)

-- | Identifiers that can be qualified by paths
data DefId = DefId { did_file     :: Text    -- ^ e.g. core/ae3efe0    
                   , did_path     :: [Entry] -- ^ e.g. ::ops[0]::function[0] 
                   , did_name     ::  Entry  -- ^ e.g. ::{{impl}}[0]   -- {{impl}}/{{clos}}
                                         --        ::T[0]          -- Trait name
                                         --        ::Option[0]     -- ADT type
                                         --        ::f[0]          -- function name, must be last
                   , did_extra    :: [Entry] -- ^ e.g. ::Some[0]       -- variant name
                                         --        ::Some[0]::0    -- field
                   }
  deriving (Eq, Ord, Generic)


isImpl :: DefId -> Bool
isImpl defid = fst (did_name defid) == "{{impl}}"


-- | If we have a static call for a trait, we need to mangle the format so that it looks
-- like a normal function call (and we can find the function handle)
mangleTraitId :: DefId -> DefId
mangleTraitId defid =
  DefId (did_file defid)
        (did_path     defid)
        ("{{impl}}", snd (did_name defid))
        (did_extra defid)

-- | Find the variant name and return it, without any decoration
cleanVariantName :: DefId -> Text
cleanVariantName defid = case did_extra defid of
   (varName, _):_ -> varName
   _              -> fst (did_name defid)


-- ret/8cd878b::E[0]::A[0]::0[0]  ==> 0
-- ret/8cd878b::S[0]::x[0]        ==> x
parseFieldName :: DefId -> Maybe Text
parseFieldName defid = case (did_extra defid) of
  [( x, _n )]      -> Just x
  [ _ , (num, _m)] -> Just num
  _ -> Nothing

-- | Detect a name that has {{impl}} in it and pull out the part after.
parseImplName :: DefId -> Maybe Entry
parseImplName defid | fst (did_name defid) == "{{impl}}" =
    case did_extra defid of
      (impl:_) -> Just impl
      _        -> Nothing
  | otherwise = Nothing

sameMethod :: Entry -> DefId -> Bool
sameMethod meth1 defid =
  case did_extra defid of
    (meth2:_) -> meth1 == meth2
    _         -> False


-- | divide the input into double colons
splitInput :: String -> [String]
splitInput str = go str [ "" ] where
    go [] strs                 = reverse (map reverse strs)
    go (':' : ':' : rest) strs = go rest ([]:strs)
    go (a : rest) (hd:strs)    = go rest ((a:hd):strs)
          

-- | recognize a string followed by a bracketted number
parseEntry :: String -> Maybe (String, Int)
parseEntry str = case Regex.matchRegex (Regex.mkRegex ( "^([{}A-Za-z0-9_]+)" ++ "\\[([0-9]+)\\]$")) str of
                  Just [idn, num] -> Just (idn, read num)
                  Nothing        -> Nothing

showEntry :: Entry -> Text
showEntry (txt,n) = pack (unpack txt ++ "[" ++ (show n) ++ "]")

-- lowercase identifiers
isPath :: String -> Bool
isPath str = isJust (Regex.matchRegex (Regex.mkRegex ( "^[a-z]+[A-Za-z0-9_]*"))  str)

           
-- | Parse text from mir-json to produce a DefId       
textId :: Text -> DefId
textId text = case splitInput (unpack text) of
  (hd : rest ) -> let (fl, entries) = case parseEntry hd of
                        Nothing -> (hd, catMaybes $ map parseEntry rest)
                        Just entry -> ("", entry: (catMaybes $ map parseEntry rest))
                      pack2 (x,y) = (pack x, y)
                  in case span (isPath . fst) entries of
                       ([], [])     -> error $ "cannot parse id " ++ unpack text
                       ([], y:ys)   -> DefId (pack fl) [] (pack2 y) (map pack2 ys)
                       (xs, [])     -> DefId (pack fl) (map pack2 (init xs)) (pack2 (last xs)) []
                       (xs, y : ys) -> DefId (pack fl) (map pack2 xs)        (pack2 y)  (map pack2 ys)
                    
  [] -> error "empty text for DefId"
                  
       

idText :: DefId -> Text
idText (DefId fl mods nm ex) =
  intercalate "::" (fl : map showEntry (mods++nm:ex))


instance Show DefId where
  show defId = unpack (idText defId)
instance IsString DefId where
  fromString str = textId (fromString str)

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
   ([("boxed", _)], ("{{impl}}",_), [("new",_)])            -> Just "new"
   ([("slice", _)], ("{{impl}}",_), [("slice_tovec",_)])    -> Just "slice_tovec"
   ([("vec", _)],   ("{{impl}}",_), [("vec_asmutslice",_)]) -> Just "vec_asmutslice"
   -- TODO add more
   _ -> Nothing


-- The relation between methods and their implementations
-- is not straightforward in MIR. The name of the function
-- implementating a method 'foo' of a trait 'Bar' by a type 'Tar'
-- looks like: '::{{impl}}[n]::foo[m]'.

{-
modid,impl,rustid,brk::String
modid = "[A-Za-z0-9]*"
impl = "{{impl}}" ++ brk
rustid = "[A-Za-z0-9]+"
brk = "\\[[0-9]+\\]"

-- | Detect a name that has {{impl}} in it and pull out the part after.
parseImplName :: String -> Maybe [String]
parseImplName = Regex.matchRegex (Regex.mkRegex $ modid ++ "::"++impl++"::("++rustid++brk++")"++".*")

-- 
parseTraitName :: String -> Maybe [String]
parseTraitName = Regex.matchRegex (Regex.mkRegex $ "(" ++rustid++")"++brk++"::"++"("++rustid++brk++")")

parseStaticMethodName :: String -> Maybe [String]
parseStaticMethodName = Regex.matchRegex (Regex.mkRegex $ "(" ++ modid ++ ")::" ++ rustid++"(" ++ brk ++ ")" ++ "::" ++ "(" ++ rustid++brk++")")

parseVariantName :: String -> Maybe [String]
parseVariantName = Regex.matchRegex (Regex.mkRegex $ modid ++ "::" ++ rustid ++ brk ++ "::" ++ "(" ++ rustid++")" ++ brk)

parseVariantName2 :: String -> Maybe [String]
parseVariantName2 = Regex.matchRegex (Regex.mkRegex $ modid ++ "::" ++ "(" ++ rustid++")" ++ brk)



cleanVariantName :: DefId -> Text
cleanVariantName txt | Just [ constrName ] <- parseVariantName (unpack (idText txt))
                     = pack constrName
                     | Just [ constrName ] <- parseVariantName2 (unpack (idText txt))
                     = pack constrName
                     | otherwise
                     = idText txt 

                     


-- If we have a static call for a trait, we need to mangle the format so that it looks like
-- a normal function call

mangleTraitId :: DefId -> DefId 
mangleTraitId defId = case parseStaticMethodName (unpack (idText defId)) of
  Just [modname,implbrk,name] -> textId $ pack (modname ++ "::" ++ "{{impl}}"++implbrk++"::"++name)    
  _ -> defId

-}              
