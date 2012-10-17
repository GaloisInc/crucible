{

module SAWScript.Parser ( parseLine, parseFile ) where

import Data.List ( head )

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST

}

%name parseDecl  Decl
%name parseDecls Decls
%tokentype { T.Token AlexPosn }
%error { parseError }
%monad { Either String } { >>= } { return }

%token
'pattern'  { T.Pattern _ _      }
'case'     { T.Keyword _ "case" }
'of'       { T.Keyword _ "of"   }
'='        { T.InfixOp _ "="    }
'->'       { T.InfixOp _ "->"   }
arrow_type { T.ArrowType _ _    }
name       { T.Identifier _ _   }
'('        { T.OutfixL _ "("    }
')'        { T.OutfixR _ ")"    }
'{'        { T.OutfixL _ "{"    }
'}'        { T.OutfixR _ "}"    }
';'        { T.InfixOp _ ";"    }
':'        { T.InfixOp _ ":"    }
'|'        { T.InfixOp _ "|"    }


%%

Expr
  : 'pattern' MaybeType          { Pattern (parsePattern (T.tokStr $1)) $2 }
  | arrow_type Args '->' Expr MaybeType 
                                 { Func (parseArrowType (T.tokStr $1)) $2 $4 $5}
  | 'case' Expr 'of' Cases MaybeType   
                                 { Switch $2 $4 $5 }
  | '{' Decls '}' MaybeType      { DM $2 $4 }
  | name MaybeType               { Var (T.tokStr $1) $2 }
  | '(' Expr ')'                 { $2 }
  | Expr Expr                    { App $1 $2 Nothing }

Decl
  : Expr          { (Nothing, $1)            }
  | name '=' Expr { (Just (T.tokStr $1), $3) }
  | arrow_type name Args MaybeType '=' Expr
      { (Just (T.tokStr $2), Func (parseArrowType (T.tokStr $1)) $3 $6 $4) }

Type
  : name           { TypeVariable (T.tokStr $1)            }
  | name '->' Type { Arrow (TypeVariable (T.tokStr $1)) $3 }

Case
  : Expr '->' Expr { ($1, $3) }

Cases
  : Case           { [$1] }
  | Case '|' Cases { $1 : $3 }

Decls
  : {- empty -}    { []      }
  | Decl           { [$1]    }
  | Decl ';' Decls { $1 : $3 }

Args
  : name                       { [((T.tokStr $1), Nothing)] }
  | name Args                  {  ((T.tokStr $1), Nothing) : $2 }
  | '(' name ':' Type ')'      { [((T.tokStr $2), Just $4)] }
  | '(' name ':' Type ')' Args {  ((T.tokStr $2), Just $4) : $6 }

MaybeType
  : {- empty -} { Nothing }
  | ':' Type    { Just $2 }

{

-- Additional Parsing

-- Warning: Assumes input matching \'[0-1]*
parsePattern :: String -> Pattern
parsePattern ('\'':bits) = Literal (map (\c -> c == '1') bits)

parseArrowType :: String -> ArrowType
parseArrowType "let" = Let
parseArrowType "fun" = Fun
parseArrowType "inj" = Inj
parseArrowType "sur" = Sur
parseArrowType "iso" = Iso

-- Error Handling

parseError tokens = Left ("Parse error: " ++ (show . head $ tokens))

-- Toplevel Parse

parseLine :: String -> Either String (Maybe String, Expr (Maybe SAWType))
parseLine s = parseDecl . alexScanTokens $ s

parseFile :: FilePath -> Either String (Maybe String, Expr (Maybe SAWType))
parseFile f = Right (Just f, DM [] Nothing) --TODO

}
