{

module SAWScript.Lexer (scan, AlexPosn) where

import Numeric
import Data.Char

import SAWScript.Token

}


%wrapper "posn"

@comment       = "/*" ([^\*]* ('*'[^\/])*)* "*/" | "//" .*

@keyword       = "import" | "as" | "let" | "and" | "fun" | "in" | "type" | "do" | "integer"

$ident_head    = [\_a-zA-Z]
$ident_tail    = [\_a-zA-Z0-9\']
@identifier    = $ident_head $ident_tail*

$base2         = 0-1
$base10        = 0-9
$base16        = [0-9a-fA-F]
@bin_lit       = "0b" $base2*
@dec_lit       = "0a" $base10*
@hex_lit       = "0x" $base16*
@integer       = $base10+

$escape        = ["\\n]
$not_escape    = ~$escape
@string        = \" ($not_escape* (\\ $escape)*)* \"

$symbol        = [\|\~\-\*\+\>\<\&\^\#\=\!\&\,\.\:\;]
@infix         = $symbol+

$outfix_left   = [\(\[\{]
$outfix_right  = [\)\]\}]

$white         = [\ \t\n\f\v\r]
$not_white     = ~$white


tokenize :-
  $white              ;
  @comment            ;
  @keyword            { Keyword     }
  @identifier         { Identifier  }
  @bin_lit            { binToBinary }
  @dec_lit            { decToBinary }
  @hex_lit            { hexToBinary }
  @integer            { Integer     }
  @string             { String      }
  @infix              { Infix       }
  $outfix_left        { OutfixL     }
  $outfix_right       { OutfixR     }
  $not_white^"."      { Postfix     }
  $not_white^"["      { Postfix     }

{

binToBinary :: AlexPosn -> String -> Token AlexPosn
binToBinary p s = Bitfield p (drop 2 s)

decToBinary :: AlexPosn -> String -> Token AlexPosn
decToBinary p s = 
  let d = read $ drop 2 s
      b = showIntAtBase 2 intToDigit d "" in
  Bitfield p b

hexToBinary :: AlexPosn -> String -> Token AlexPosn
hexToBinary p s = Bitfield p (concat $ map (\c -> case c of {
  '0' -> "0000" ; '1' -> "0001" ; '2' -> "0010" ; '3' -> "0011";
  '4' -> "0100" ; '5' -> "0101" ; '6' -> "0110" ; '7' -> "0111";
  '8' -> "1000" ; '9' -> "1001" ; 'a' -> "1010" ; 'b' -> "1011";
  'c' -> "1100" ; 'd' -> "1101" ; 'e' -> "1110" ; 'f' -> "1111" }) (drop 2 s))

scan = alexScanTokens

}