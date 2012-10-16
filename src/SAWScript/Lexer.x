{

module SAWScript.Lexer where

import Data.Char

import SAWScript.Token
import SAWScript.AST

}


%wrapper "posn"

$newline      = [\n\r]
$bit          = 0-1
$operator     = [\|\~\-\*\+\>\<\&\^\#\=\!\&\.\:\;]
$idents       = [a-zA-Z0-9]
$outfix_left  = [\(\[\{]
$outfix_right = [\)\]\}]

@ws                 = $white+
@bitfield           = \' $bit*
@identifier         = $idents+
@function_keyword   = "let" | "fun" | "inj" | "sur" | "iso"
@all_keywords       = @function_keyword | "case" | "of"
@arrow_or_equals    = "->" | "="
@function_signature = @function_keyword (@ws @identifier)+ @ws* @arrow_or_equals

tokenize :-
@ws            ;
@bitfield      { BitField   }
@identifier    { Identifier }
$operator+     { InfixOp    }
$outfix_left   { OutfixL }
$outfix_right  { OutfixR }











{

}