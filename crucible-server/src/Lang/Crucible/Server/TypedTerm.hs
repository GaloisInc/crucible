{- |
Module      : $Header$
Description : SAW-Core terms paired with Cryptol types.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module Lang.Crucible.Server.TypedTerm where

import Data.Map (Map)
import qualified Data.Map as Map

import Cryptol.ModuleSystem.Name (nameIdent)
import qualified Cryptol.TypeCheck.AST as C
import Cryptol.Utils.PP (pretty, text, PP(..))

import Verifier.SAW.Cryptol (scCryptolType)
import Verifier.SAW.SharedTerm

-- Typed terms -----------------------------------------------------------------

{- Within SAWScript, we represent an object language term as a SAWCore
shared term paired with a Cryptol type schema. The Cryptol type is
used for type inference/checking of inline Cryptol expressions. -}

data TypedTerm =
  TypedTerm
  { ttSchema :: C.Schema
  , ttTerm :: Term
  }
  deriving Show

ttTermLens :: Functor f => (Term -> f Term) -> TypedTerm -> f TypedTerm
ttTermLens f tt = tt `seq` fmap (\x -> tt{ttTerm = x}) (f (ttTerm tt))

mkTypedTerm :: SharedContext -> Term -> IO TypedTerm
mkTypedTerm sc trm = do
  ty <- scTypeOf sc trm
  ct <- scCryptolType sc ty
  return $ TypedTerm (C.Forall [] [] ct) trm

-- Ugh...
instance PP TypedTerm where
  ppPrec _i (TypedTerm _ x) = text (scPrettyTerm defaultPPOpts x)


-- Typed modules ---------------------------------------------------------------

{- In SAWScript, we can refer to a Cryptol module as a first class
value. These are represented simply as maps from names to typed
terms. -}

data CryptolModule =
  CryptolModule (Map C.Name C.TySyn) (Map C.Name TypedTerm)

showCryptolModule :: CryptolModule -> String
showCryptolModule (CryptolModule sm tm) =
  unlines $
    (if Map.null sm then [] else
       "Type Synonyms" : "=============" : map showTSyn (Map.elems sm) ++ [""]) ++
    "Symbols" : "=======" : map showBinding (Map.assocs tm)
  where
    showTSyn (C.TySyn name params _props rhs _doc) =
      "    " ++ unwords (pretty (nameIdent name) : map pretty params) ++ " = " ++ pretty rhs
    showBinding (name, TypedTerm schema _) =
      "    " ++ pretty (nameIdent name) ++ " : " ++ pretty schema
