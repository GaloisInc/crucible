{

module SAWScript.Lexer where

import Data.Char

import SAWScript.Token

}


%wrapper "posn"

$newline      = [\n\r]
$bit          = 0-1
$operator     = [\|\~\-\*\+\>\<\&\^\#\=\!\&\.\:\;]
$idents       = [a-zA-Z0-9]
$outfix_left  = [\(\[\{]
$outfix_right = [\)\]\}]

@ws                 = $white+
@pattern            = \' $bit*
@identifier         = $idents+
@arrow_type         = "let" | "fun" | "inj" | "sur" | "iso"
@keyword            = "case" | "of"

tokenize :-
@ws            ;
@pattern       { Pattern    }
@arrow_type    { ArrowType  }
@keyword       { Keyword    }
@identifier    { Identifier }
$operator+     { InfixOp    }
$outfix_left   { OutfixL    }
$outfix_right  { OutfixR    }











{

}