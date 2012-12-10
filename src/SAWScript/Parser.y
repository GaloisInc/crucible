{

module SAWScript.Parser ( parse ) where

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST
import SAWScript.FixFunctor
import Control.Applicative

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
'string'                                { T.Keyword    _ "string"  }
'bit'                                   { T.Keyword    _ "bit"     }
unit                                    { T.Keyword    _ "()"      }
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

TopStatements :: { [TopStmt MPType] }
 : {- Nothing -}                  { []    }
 | TopStatement ';' TopStatements { $1:$3 }

TopStatement :: { TopStmt MPType }
 : 'let' Declarations1                  { TopLet $2         }
 | name '::' CType                      { TopTypeDecl $1 $3 }
 | 'type' name '=' CType                { TypeDef $2 $4     }
 | 'import' Import                      { $2                }

BlockStatement :: { BlockStmt MPType }
 : Expr                { Bind Nothing $1     }
 | name '=' Expr       { Bind (Just $1) $3   }
 | name '::' CType     { BlockTypeDecl $1 $3 }
 | 'let' Declarations1 { BlockLet $2         }

Declaration :: { (Name, Expr MPType) }
 : name Args '=' Expr                   { ($1, buildFunction $2 $4)       }

Import :: { TopStmt MPType }
 : name                                 { Import $1 Nothing Nothing       }
 | name '(' CommaSepNames ')'           { Import $1 (Just $3) Nothing     }
 | name 'as' name                       { Import $1 Nothing (Just $3)     }
 | name '(' CommaSepNames ')' 'as' name { Import $1 (Just $3) (Just $6)   }

Arg :: { (Name, MPType) }
 : name                                 { ($1, Nothing) }
 | '(' name ':' PType ')'               { ($2, Just $4) }

Expr :: { Expr MPType }
 : Exprs MaybeType { updateAnnotation (buildApplication $1) $2 }

Exprs :: { [Expr MPType] }
 : Primitive { [$1] }
 | SafePrimitive Exprs { $1:$2 }

Primitive :: { Expr MPType }
 : UnsafePrimitive  { $1 }
 | SafePrimitive    { $1 }

UnsafePrimitive :: { Expr MPType }
 : 'fun' Args1 '->' Expr                { buildFunction $2 $4           }
 | 'let' Declarations1 'in' Expr        { LetBlock $2 $4                }
 | SafePrimitive infixOp Expr                    
    { Application (Application (Var $2 Nothing ) $1 Nothing) $3 Nothing }

SafePrimitive :: { Expr MPType }
 : unit   MaybeType                     { Unit $2                       }
 | bits   MaybeType                     { Array (bitsOfString $1) $2    }
 | string MaybeType                     { Quote $1 $2                   }
 | int    MaybeType                     { Z (read $1) $2                }
 | name   MaybeType                     { Var $1 $2                     }
 | '(' Expr ')'                         { $2                            }
 | ' [' CommaSepExprs ']' MaybeType     { Array $2 $4                   }
 | '{' CommaSepFields '}' MaybeType     { Record $2 $4                  }
 | 'do' '{' SemiSepBlockStmts '}'       { Block $3 Nothing              }
 | SafePrimitive '.' name MaybeType     { Lookup $1 $3 $4               }
 | SafePrimitive '[' Expr ']' MaybeType { Index $1 $3 $5                }

Field :: { (Name, Expr MPType) }
 : name ':' Expr                        { ($1, $3) }
 | string ':' Expr                      { ($1, $3) }

CType :: { CType }
 : 'integer'                            { z                   }
 | 'string'                             { quote               }
 | 'bit'                                { bit                 }
 | name                                 { syn $1              }
 |  '[' int ']'                         { array bit (read $2) }
 | ' [' int ']'                         { array bit (read $2) }
 |  '[' int ']' CType                   { array $4  (read $2) }
 | ' [' int ']' CType                   { array $4  (read $2) }
PType :: { PType }
 : 'integer'                            { z                   }
 | 'string'                             { quote               }
 | 'bit'                                { bit                 }
 | name                                 { syn $1              }
 |  '[' int ']'                         { array bit (read $2) }
 | ' [' int ']'                         { array bit (read $2) }
 |  '[' int ']' PType                   { array $4  (read $2) }
 | ' [' int ']' PType                   { array $4  (read $2) }
 | '(' CommaSepPTypes ')'               { tuple $2            }
 | PType '->' PType                     { function $1 $3      }

CommaSepPTypes :: { [PType] }
 : {- Nothing -}                        { [] }
 | PType ',' CommaSepPTypes             { $1:$3 }

MaybeType :: { MPType }
 : {- Nothing -}                        { Nothing }
 | ':' PType                            { Just $2 }

Declarations1 :: { [(Name, Expr MPType)] }
 : Declaration                          { [$1]  }
 | Declaration 'and' Declarations1      { $1:$3 }

Args :: { [(Name, MPType)] }
 : {- Nothing -}                        { [] }
 | Args1                                { $1 }

Args1 :: { [(Name, MPType)] }
 : Arg                                  { [$1]  }
 | Arg Args1                            { $1:$2 }

SemiSepBlockStmts :: { [BlockStmt MPType] }
 : {- Nothing -}                        { []    }
 | BlockStatement ';' SemiSepBlockStmts { $1:$3 }

CommaSepExprs :: { [Expr MPType] }
 : {- Nothing -}                        { [] }
 | CommaSepExprs1                       { $1 }

CommaSepExprs1 :: { [Expr MPType] }
 : Expr                                 { [$1] }
 | Expr ',' CommaSepExprs1              { $1:$3 }

CommaSepFields :: { [(Name, Expr MPType)] }
 : {- Nothing -}                        { [] }
 | CommaSepFields1                      { $1 }

CommaSepFields1 :: { [(Name, Expr MPType)] }
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

bitsOfString :: String -> [Expr MPType]
bitsOfString = (map (\b -> Bit b (Just bit))) . (map (/='0'))

buildFunction :: [(Name, MPType)] -> Expr MPType -> Expr MPType 
buildFunction args e = 
  let foldFunction (argumentName, maybeType) rhs = 
        Function argumentName maybeType e (function <$> maybeType <*> (annotation rhs)) in
  foldr foldFunction e args

buildApplication :: [Expr MPType] -> Expr (MPType)
buildApplication [e]    = e
buildApplication (e:es) = 
  let app' = buildApplication es in
  Application e (app') (function <$> (annotation e) <*> (annotation app'))
}
