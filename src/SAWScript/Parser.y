{

module SAWScript.Parser ( read ) where

import Prelude hiding ( read )
import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST

}

%name read
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
bits                                    { T.Bitfield   _ $$        }
string                                  { T.String     _ $$        }
int                                     { T.Integer    _ $$        }
name                                    { T.Identifier _ $$        }

%%

Statement
 : 'let' Declarations1                  { Declarations $2   }
 | name '::' Type                       { ForwardDecl $1 $3 }
 | name Exprs                           { Command $1 $2     }
 | 'type' name '=' Type                 { Typedef $2 $4     }
 | 'import' Import                      { $2                }

Declaration
 : name Args MaybeType '=' Expr         { Declaration $1 $2 $5 $3 }

Import
 : name                                 { Import $1 Nothing Nothing     }
 | name '(' CommaSepNames ')'           { Import $1 (Just $3) Nothing   }
 | name 'as' name                       { Import $1 Nothing (Just $3)   }
 | name '(' CommaSepNames ')' 'as' name { Import $1 (Just $3) (Just $6) }

Arg
 : name                                 { ($1, Nothing) }
 | '(' name ':' Type ')'                { ($2, Just $4) }

Expr 
 : UnsafeExpr                           { $1 }
 | SafeExpr                             { $1 }

UnsafeExpr
 : 'fun' Args MaybeType '->' Expr       { Function $2 $5 $3         }
 | SafeExpr Exprs1                      { Application $1 $2 Nothing }
 | 'let' Declarations1 'in' Expr        { LetBlock $2 $4            }

SafeExpr
 : bits   MaybeType                     { Bitfield (bitsOfString $1) $2 }
 | string MaybeType                     { Quote $1 $2                   }
 | int    MaybeType                     { Z (read $1) $2                }
 | name   MaybeType                     { Var $1 $2                     }
 | Record MaybeType                     { Record $1 $2                  }
 | '(' Expr ')'                         { $2                            }
 | '(' UnsafeExpr ')' MaybeType         { Application $2 $3 $5          }
 | ' [' CommaSepExprs ']'               { Array $2                      }
 | 'do' '{' SemiSepStatements '}'       { Procedure $3 Nothing          }
 | SafeExpr '.' name                    { Lookup $1 $3                  }
 | SafeExpr '[' Expr ']'                { Index $1 $3                   }

Record
 : '{' CommaSepFields '}'               { Record $2 }

Field
 : name ':' Expr                        { ($1, $3) }
 | string ':' Expr                      { ($1, $3) }

Type
 : 'integer'                            { Z' }
 | name                                 { Var' $1 }
 |  '[' int ']'                         { Bitfield' (read $2) }
 | ' [' int ']'                         { Bitfield' (read $2) }
 |  '[' Type ']'                        { Array' $2 Nothing }
 | ' [' Type ']'                        { Array' $2 Nothing }

MaybeType
 : {- Nothing -}                        { Nothing }
 | ':' Type                             { Just $2 }

Declarations1
 : Declaration                          { [$1]  }
 | Declaration 'and' Declarations1      { $1:$3 }

Args
 : {- Nothing -}                        { [] }
 | Args1                                { $1 }

Args1
 : Arg                                  { [$1]  }
 | Arg Args1                            { $1:$2 }

SemiSepStatements
  : {- Nothing -}                       { []    }
  | Statement ';' SemiSepStatements     { $1:$3 }

Exprs
 : {- Nothing -}                        { [] }
 | Exprs1                               { $1 }

Exprs1
 : Expr                                 { [$1]    }
 | SafeExpr Exprs1                      { $1:$2 }

CommaSepExprs
 : {- Nothing -}                        { [] }
 | CommaSepExprs1                       { $1 }

CommaSepExprs1
 : Expr                                 { [$1] }
 | Expr ',' CommaSepExprs1              { $1:$3 }

CommaSepFields
 : {- Nothing -}                        { [] }
 | CommaSepFields1                      { $1 }

CommaSepFields1
 : Field                                { [$1]  }
 | Field ',' CommaSepFields1            { $1:$3 }

CommaSepNames
  : {- Nothing -}                       { [] }
  | CommaSepNames1                      { $1 }

CommaSepNames1 
  : name                                { [$1] }
  | name ',' CommaSepNames1             { $1:$3  }

{

parseError :: [T.Token a] -> b
parseError _ = error "Parse error"

bitsOfString :: String -> [Bool]
bitsOfString = map (/='0')

}