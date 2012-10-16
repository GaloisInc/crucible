{

module SAWScript.Parser ( stringToExpr ) where

import Data.List ( head )

import SAWScript.Token
import SAWScript.Lexer
import SAWScript.AST

}

%name parseExpr
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Either String } { >>= } { return }

%token
'bitfield' { BitField _ _ }
'='        { InfixOp _ "=" }
name       { Identifier _ _ }
'{'        { OutfixL _ "{" }
'}'        { OutfixR _ "}" }
';'        { InfixOp _ ";" }


%%


Expr 
  : 'bitfield'    { BitLiteral (parseBits (tokStr $1)) }
  | name '=' Expr { Binder (tokStr $1) $3 }
  | '{' Exprs '}' { Bag $2 }

Exprs
  : {- empty -}    { [] }
  | Expr           { [$1] }
  | Expr ';' Exprs { $1 : $3 }

{

-- Additional Parsing

-- Warning: Assumes input matching \'[0-1]*
parseBits :: String -> [Bool]
parseBits ('\'':bits) = map (\c -> c == '1') bits

-- Error Handling

parseError tokens = Left ("Parse error: " ++ (show . head $ tokens))

-- Toplevel Parse

stringToExpr :: String -> Either String Expr
stringToExpr = parseExpr . alexScanTokens

}
