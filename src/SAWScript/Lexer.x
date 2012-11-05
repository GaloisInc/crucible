{

module SAWScript.Lexer where

import Data.Char

import SAWScript.Token

}


%wrapper "posn"

$newline       = [\n\r]
$ws            = [\ \b\t\n\f\v\r]
$nws           = [^\ \b\t\n\f\v\r]
$bit           = 0-1
$dec           = 0-9
$hex           = [0-9a-fA-F]
$operator      = [\|\~\-\*\+\>\<\&\^\#\=\!\&\.\:\;]
$idents        = [a-zA-Z0-9\']
$alpha         = [a-zA-Z]
$outfix_left   = [\(\[\{]
$outfix_right  = [\)\]\}]


@keyword      = "import" | "as" | "let" | "in" | "type" | "do"
@ws           = $white+
@pattern      = \' $bit*
@identifier   = $idents+
@index        = "[" | "." @identifier
@binary_lit   = "0b" $bit*
@dec_lit      = "0a" $dec*
@hex_lit      = "0x" $hex*


tokenize :-
@ws            ;
@pattern       { Pattern    }
@keyword       { Keyword    }
@identifier    { Identifier }
$operator+     { InfixOp    }
$outfix_left   { OutfixL    }
$outfix_right  { OutfixR    }
$nws^ "." @identifier { Postfix }
$nws^ "["      { Postfix }










{

}