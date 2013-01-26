{

module SAWScript.Lexer
  ( AlexPosn(..)
  , scan
  ) where

import SAWScript.Compiler
import SAWScript.AST
import SAWScript.Token

import Numeric
import Data.Char
import Data.List

}


%wrapper "monad"

$allChars      = [\x00-\x10ffff]
@comment       = ("/*"   (($allChars # [\*]) | ("*" ($allChars # [\/])))*  "*/") | ("//" .*)


@keyword       = "()" | "import" | "as" | "let" | "and" | "fun" | "in" | "type" | "do" | "integer" | "string" | "bit"

$ident_head    = [\_a-zA-Z]
$ident_tail    = [\_a-zA-Z0-9\'\.]
@identifier    = $ident_head $ident_tail*

$base2         = 0-1
$base10        = 0-9
$base16        = [0-9a-fA-F]
@bin_lit       = "0b" $base2*
@dec_lit       = "0a" $base10*
@hex_lit       = "0x" $base16*
@integer       = $base10+


$escape        = ["\\n]                                    
--"
$not_escape    = ~$escape
@string        = \" ([^\\]* (\\ $escape)*)* \"

$symbol        = [\|\~\-\*\+\>\<\&\^\#\=\!\&\,\.\:\;]
@infix         = $symbol+

$outfix_left   = [\(\[\{]
$outfix_right  = [\)\]\}]

$white         = [\ \t\n\f\v\r]
$not_white     = ~$white



tokenize :-
  $white              ;
  @comment            ;
  @keyword            { expr Keyword     }
  @identifier         { expr Identifier  }
  @bin_lit            {      binToBinary }
  @dec_lit            {      decToBinary }
  @hex_lit            {      hexToBinary }
  @integer            { expr Integer     }
  @string             { expr String      }
  @infix              { expr Infix       }
  $not_white^"."      { expr Postfix     }
  $not_white^"["      { expr Postfix     }
  $outfix_left        { expr OutfixL     }
  $outfix_right       { expr OutfixR     }

{

type Action = AlexAction (Token AlexPosn)

expr :: TokenClass -> Action
expr tc (pos,_,_,str) len = return $ Token tc pos $ take len str

binToBinary :: Action
binToBinary (pos,_,_,str) len = return $ Token Bitfield pos $ drop 2 $ take len str

decToBinary :: Action
decToBinary (pos,_,_,str) len = return $ Token Bitfield pos b
  where
  d = read $ drop 2 $ take len str
  b = showIntAtBase 2 intToDigit d ""

hexToBinary :: Action
hexToBinary (pos,_,_,str) len = return $ Token Bitfield pos $
  concatMap (hexToBinBit . toLower) $ drop 2 $ take len str
  where
  hexToBinBit :: Char -> String
  hexToBinBit c = case c of
    '0' -> "0000" 
    '1' -> "0001" 
    '2' -> "0010" 
    '3' -> "0011"
    '4' -> "0100" 
    '5' -> "0101" 
    '6' -> "0110" 
    '7' -> "0111"
    '8' -> "1000" 
    '9' -> "1001" 
    'a' -> "1010" 
    'b' -> "1011"
    'c' -> "1100" 
    'd' -> "1101" 
    'e' -> "1110" 
    'f' -> "1111"

alexEOF = return (Token EOF undefined "")

scan :: Compiler String [Token AlexPosn]
scan input = case runAlex input loop of
  Left err  -> fail (intercalate "\n" [err ++ ":",input])
  Right yay -> return yay
  where
  loop = do
    tok <- alexMonadScan
    if tokClass tok == EOF
      then return []
      else do
        rest <- loop
        return (tok : rest)


}
