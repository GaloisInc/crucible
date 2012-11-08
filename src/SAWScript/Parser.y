{

module SAWScript.Parser ( parse ) where

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST

}

%name parse
%error { parseError }
%tokentype { T.Token AlexPosn }

%token
'import'                                { T.Keyword    _ "import"  }
'as'                                    { T.Keyword    _ "as"      }
'let'                                   { T.Keyword    _ "let"     }
'and'                                   { T.Keyword    _ "and"     }
'fun'                                   { T.Keyword    _ "fun"     }
'in'                                    { T.Keyword    _ "in"      }
'type'                                  { T.Keyword    _ "type"    }
'do'                                    { T.Keyword    _ "do"      }
'integer'                               { T.Keyword    _ "integer" }
'='                                     { T.Infix      _ "="       }
'->'                                    { T.Infix      _ "->"      }
';'                                     { T.Infix      _ ";"       }
','                                     { T.Infix      _ ","       }
':'                                     { T.Infix      _ ":"       }
'::'                                    { T.Infix      _ "::"      }
'('                                     { T.OutfixL    _ "("       }
')'                                     { T.OutfixR    _ ")"       }
' ['                                    { T.OutfixL    _ "["       }
']'                                     { T.OutfixR    _ "]"       }
'{'                                     { T.OutfixL    _ "{"       }
'}'                                     { T.OutfixR    _ "}"       }
'['                                     { T.Postfix    _ "["       }
'.'                                     { T.Postfix    _ "."       }
infixOp                                 { T.Infix      _ $$        }
bits                                    { T.Bitfield   _ $$        }
string                                  { T.String     _ $$        }
int                                     { T.Integer    _ $$        }
name                                    { T.Identifier _ $$        }

%%

Statement :: { Statement (Maybe Type) }
 : 'let' Declarations1                  { Declarations $2   }
 | name '::' Type                       { ForwardDecl $1 $3 }
 | 'type' name '=' Type                 { Typedef $2 $4     }
 | 'import' Import                      { $2                }
 | Expr                                 { Command $1        }

Declaration :: { Declaration (Maybe Type) }
 : name Args MaybeType '=' Expr         { Declaration $1 $2 $5 $3 }

Import :: { Statement (Maybe Type) }
 : name                                 { Import $1 Nothing Nothing     }
 | name '(' CommaSepNames ')'           { Import $1 (Just $3) Nothing   }
 | name 'as' name                       { Import $1 Nothing (Just $3)   }
 | name '(' CommaSepNames ')' 'as' name { Import $1 (Just $3) (Just $6) }

Arg :: { (Name, Maybe Type) }
 : name                                 { ($1, Nothing) }
 | '(' name ':' Type ')'                { ($2, Just $4) }

Expr :: { Expr (Maybe Type) }
 : Primitive   { $1 }
 | Application { $1 }

Primitive :: { Expr (Maybe Type) }
 : UnsafePrimitive  { $1 }
 | SafePrimitive    { $1 }

Application :: { Expr (Maybe Type) }
 : SafePrimitive Primitive   { Application $1 $2 Nothing }
 | Application Primitive     { Application $1 $2 Nothing }

UnsafePrimitive :: { Expr (Maybe Type) }
 : 'fun' Args1 MaybeType '->' Expr      { uncurryFunction $2 $3 $5      }
 | 'let' Declarations1 'in' Expr        { LetBlock $2 $4                }
 | SafePrimitive infixOp Expr                    
    { Application (Application (Var $2 Nothing ) $1 Nothing) $3 Nothing }

SafePrimitive :: { Expr (Maybe Type) }
 : bits   MaybeType                     { Array (bitsOfString $1) $2    }
 | string MaybeType                     { Quote $1 $2                   }
 | int    MaybeType                     { Z (read $1) $2                }
 | name   MaybeType                     { Var $1 $2                     }
 | '(' Expr ')'                         { $2                            }
 | ' [' CommaSepExprs ']' MaybeType     { Array $2 $4                   }
 | '{' CommaSepFields '}' MaybeType     { Record $2 $4                  }
 | 'do' '{' SemiSepStatements '}'       { Procedure $3 Nothing          }
 | SafePrimitive '.' name MaybeType     { Lookup $1 $3 $4               }
 | SafePrimitive '[' Expr ']' MaybeType { Index $1 $3 $5                }

Field :: { (Name, Expr (Maybe Type)) }
 : name ':' Expr                        { ($1, $3) }
 | string ':' Expr                      { ($1, $3) }

Type :: { Type }
 : 'integer'                            { Z'                    }
 | name                                 { Var' $1               }
 |  '[' int ']'                         { Array' Bit' (read $2) }
 | ' [' int ']'                         { Array' Bit' (read $2) }
 |  '[' Type ']'                        { Array' $2 Nothing     }
 | ' [' Type ']'                        { Array' $2 Nothing     }

MaybeType :: { Maybe Type }
 : {- Nothing -}                        { Nothing }
 | ':' Type                             { Just $2 }

Declarations1 :: { [Declaration (Maybe Type)] }
 : Declaration                          { [$1]  }
 | Declaration 'and' Declarations1      { $1:$3 }

Args :: { [(Name, Maybe Type)] }
 : {- Nothing -}                        { [] }
 | Args1                                { $1 }

Args1 :: { [(Name, Maybe Type)] }
 : Arg                                  { [$1]  }
 | Arg Args1                            { $1:$2 }

SemiSepStatements :: { [Statement (Maybe Type)] }
 : {- Nothing -}                       { []    }
 | Statement ';' SemiSepStatements     { $1:$3 }

CommaSepExprs :: { [Expr (Maybe Type)] }
 : {- Nothing -}                        { [] }
 | CommaSepExprs1                       { $1 }

CommaSepExprs1 :: { [Expr (Maybe Type)] }
 : Expr                                 { [$1] }
 | Expr ',' CommaSepExprs1              { $1:$3 }

CommaSepFields :: { [(Name, Expr (Maybe Type))] }
 : {- Nothing -}                        { [] }
 | CommaSepFields1                      { $1 }

CommaSepFields1 :: { [(Name, Expr (Maybe Type))] }
 : Field                                { [$1]  }
 | Field ',' CommaSepFields1            { $1:$3 }

CommaSepNames :: { [Name] }
  : {- Nothing -}                       { [] }
  | CommaSepNames1                      { $1 }

CommaSepNames1 :: { [Name] }
  : name                                { [$1] }
  | name ',' CommaSepNames1             { $1:$3  }

{

parseError :: [T.Token a] -> b
parseError _ = error "Parse error"

bitsOfString :: String -> [Expr (Maybe Type)]
bitsOfString = (map (\b -> Bit b (Just Bit'))) . (map (/='0'))

uncurryFunction :: [(Name, Maybe Type)] -> Maybe Type -> Expr (Maybe Type) -> Expr (Maybe Type)
uncurryFunction [a]    mt e = Function a e mt
uncurryFunction (a:as) mt e = Function a (uncurryFunction as mt e) Nothing

}