{-|
Copyright   : (c) Galois Inc, 2015
License     : BSD3
Maintainer  : jhendrix@galois.com

This defines a datatype for representing identifiers that can be
used with Crucible.  These must start with an ASCII letter and can consist
of any characters in the set @['a'-'z' 'A'-'Z' '0'-'9' '_']@ as long as the
result is not an SMTLIB or Yices keyword.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module What4.Symbol
  ( SolverSymbol
  , solverSymbolAsText
  , SolverSymbolError
  , emptySymbol
  , userSymbol
  , systemSymbol
  , ppSolverSymbolError
  ) where

import           Data.Char
import           Data.Hashable
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text

isAsciiLetter :: Char -> Bool
isAsciiLetter c
  =  'A' <= c && c <= 'Z'
  || 'a' <= c && c <= 'z'

isSymbolChar :: Char -> Bool
isSymbolChar c
  = isAsciiLetter c
  || isDigit c
  || c == '_'
  || c == '\''
  || c == '!'

-- | This describes why a given text value was not a valid solver symbol.
data SolverSymbolError
   = SymbolEmpty
   | SymbolNoStartWithChar
   | SymbolIllegalChar
   | SymbolSMTLIBReserved
   | SymbolYicesReserved

instance Show SolverSymbolError where
  show e = "Identifier " ++ ppSolverSymbolError e


ppSolverSymbolError :: SolverSymbolError -> String
ppSolverSymbolError e =
  case e of
    SymbolEmpty           -> "cannot be empty."
    SymbolNoStartWithChar -> "must start with a letter."
    SymbolIllegalChar     -> "contains an illegal character."
    SymbolSMTLIBReserved  -> "is an SMTLIB reserved word."
    SymbolYicesReserved   -> "is a Yices reserved word."


-- | This represents a name known to the solver.
--
-- We have three types of symbols:
--
-- * The empty symbol
--
-- * A user symbol
--
-- * A system symbol
--
-- A user symbol should consist of a letter followed by any combination
-- of letters, digits, and underscore characters.  It also cannot be a reserved
-- word in Yices or SMTLIB.
--
-- A system symbol should start with a letter followed by any number of
-- letter, digit, underscore or an exclamation mark characters.  It must
-- contain at least one exclamation mark to distinguish itself from user
-- symbols.
newtype SolverSymbol = SolverSymbol { solverSymbolAsText :: Text }
  deriving (Eq, Ord, Hashable)

-- | Return the empty symbol
emptySymbol :: SolverSymbol
emptySymbol = SolverSymbol Text.empty

-- | This returns either a user symbol or the empty symbol if the string is empty.
userSymbol :: String -> Either SolverSymbolError SolverSymbol
userSymbol s
  | elem '!' s = Left SymbolIllegalChar
  | otherwise = parseAnySymbol s

systemSymbol :: String -> SolverSymbol
systemSymbol s
    -- System symbols must contain an exclamation mark to distinguish them from
    -- user symbols (which are not allowed to have exclamation marks).
  | '!' `notElem` s =
    error $
      "The system symbol " ++ show s ++ " must contain at least one exclamation mark '!'"
  | otherwise =
    case parseAnySymbol s of
      Left e -> error ("Error parsing system symbol " ++ show s ++ ": " ++ ppSolverSymbolError e)
      Right r -> r

instance Show SolverSymbol where
  show s = Text.unpack (solverSymbolAsText s)

-- | This attempts to parse a string as a valid solver symbol.
parseAnySymbol :: String -> Either SolverSymbolError SolverSymbol
parseAnySymbol [] = Right emptySymbol
parseAnySymbol (h:r)
  | isAsciiLetter h == False          = Left SymbolNoStartWithChar
  | all isSymbolChar r == False       = Left SymbolIllegalChar
  | t `Set.member` smtlibKeywordSet   = Left SymbolSMTLIBReserved
  | t `Set.member` yicesKeywordSet    = Left SymbolYicesReserved
  | otherwise = Right (SolverSymbol t)
  where t = if elem '\'' r
            then fromString ("|" ++ (h:r) ++ "|")
            else fromString (h:r)

smtlibKeywordSet :: Set Text
smtlibKeywordSet = Set.fromList (fromString <$> smtlibKeywords)

yicesKeywordSet :: Set Text
yicesKeywordSet = Set.fromList (fromString <$> yicesKeywords)

-- | This is the list of keywords in SMTLIB 2.5
smtlibKeywords :: [String]
smtlibKeywords =
  [ "BINARY"
  , "DECIMAL"
  , "HEXADECIMAL"
  , "NUMERAL"
  , "STRING"
  , "as"
  , "let"
  , "exists"
  , "forall"
  , "par"
  , "assert"
  , "check-sat"
  , "check-sat-assuming"
  , "declare-const"
  , "declare-fun"
  , "declare-sort"
  , "define-fun"
  , "define-fun-rec"
  , "define-funs-rec"
  , "define-sort"
  , "echo"
  , "exit"
  , "get-assertions"
  , "get-assignment"
  , "get-info"
  , "get-model"
  , "get-option"
  , "get-proof"
  , "get-unsat-assumptions"
  , "get-unsat-core"
  , "get-value"
  , "pop"
  , "push"
  , "reset"
  , "reset-assertions"
  , "set-info"
  , "set-logic"
  , "set-option"
  ]

yicesKeywords :: [String]
yicesKeywords =
  [ "abs"
  , "and"
  , "assert"
  , "bit"
  , "bitvector"
  , "bool"
  , "bool-to-bv"
  , "bv-add"
  , "bv-and"
  , "bv-ashift-right"
  , "bv-ashr"
  , "bv-comp"
  , "bv-concat"
  , "bv-div"
  , "bv-extract"
  , "bv-ge"
  , "bv-gt"
  , "bv-le"
  , "bv-lshr"
  , "bv-lt"
  , "bv-mul"
  , "bv-nand"
  , "bv-neg"
  , "bv-nor"
  , "bv-not"
  , "bv-or"
  , "bv-pow"
  , "bv-redand"
  , "bv-redor"
  , "bv-rem"
  , "bv-repeat"
  , "bv-rotate-left"
  , "bv-rotate-right"
  , "bv-sdiv"
  , "bv-sge"
  , "bv-sgt"
  , "bv-shift-left0"
  , "bv-shift-left1"
  , "bv-shift-right0"
  , "bv-shift-right1"
  , "bv-shl"
  , "bv-sign-extend"
  , "bv-sle"
  , "bv-slt"
  , "bv-smod"
  , "bv-srem"
  , "bv-sub"
  , "bv-xnor"
  , "bv-xor"
  , "bv-zero-extend"
  , "ceil"
  , "check"
  , "define"
  , "define-type"
  , "distinct"
  , "div"
  , "divides"
  , "dump-context"
  , "echo"
  , "ef-solve"
  , "eval"
  , "exists"
  , "exit"
  , "export-to-dimacs"
  , "false"
  , "floor"
  , "forall"
  , "help"
  , "if"
  , "include"
  , "int"
  , "is-int"
  , "ite"
  , "lambda"
  , "let"
  , "mk-bv"
  , "mk-tuple"
  , "mod"
  , "not"
  , "or"
  , "pop"
  , "push"
  , "real"
  , "reset"
  , "reset-stats"
  , "scalar"
  , "select"
  , "set-param"
  , "set-timeout"
  , "show-implicant"
  , "show-model"
  , "show-param"
  , "show-params"
  , "show-stats"
  , "true"
  , "tuple"
  , "tuple-update"
  , "update"
  , "xor"
  ]
