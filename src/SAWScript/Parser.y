{

module SAWScript.Parser ( parse ) where

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST
import SAWScript.FixFunctor

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
 : name Args MaybeType '=' Expr         { ($1, uncurryFunction $2 $3 $5) }

Import :: { TopStmt MPType }
 : name                                 { Import $1 Nothing Nothing     }
 | name '(' CommaSepNames ')'           { Import $1 (Just $3) Nothing   }
 | name 'as' name                       { Import $1 Nothing (Just $3)   }
 | name '(' CommaSepNames ')' 'as' name { Import $1 (Just $3) (Just $6) }

Arg :: { (Name, MPType) }
 : name                                 { ($1, Nothing) }
 | '(' name ':' PType ')'                { ($2, Just $4) }

Expr :: { Expr MPType }
 : Primitive   { $1 }
 | Application { $1 }

Primitive :: { Expr MPType }
 : UnsafePrimitive  { $1 }
 | SafePrimitive    { $1 }

Application :: { Expr MPType }
 : SafePrimitive Primitive   { Application $1 $2 Nothing }
 | Application Primitive     { Application $1 $2 Nothing }

UnsafePrimitive :: { Expr MPType }
 : 'fun' Args1 MaybeType '->' Expr      { uncurryFunction $2 $3 $5      }
 | 'let' Declarations1 'in' Expr        { LetBlock $2 $4                }
 | SafePrimitive infixOp Expr                    
    { Application (Application (Var $2 Nothing ) $1 Nothing) $3 Nothing }

SafePrimitive :: { Expr MPType }
 : bits   MaybeType                     { Array (bitsOfString $1) $2    }
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
 | name                                 { syn $1              }
 |  '[' int ']'                         { array bit (read $2) }
 | ' [' int ']'                         { array bit (read $2) }
 |  '[' int ']' CType                   { array $4  (read $2) }
PType :: { PType }
 : 'integer'                            { z                   }
 | name                                 { syn $1              }
 |  '[' int ']'                         { array bit (read $2) }
 | ' [' int ']'                         { array bit (read $2) }

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

SemiSepTopStmts :: { [TopStmt MPType] }
 : {- Nothing -}                        { [] }
 | TopStatement ';' SemiSepTopStmts     { $1:$3 }

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

-- 'FIXME: Insert the mt argument correctly
uncurryFunction :: [(Name, MPType)] -> MPType -> Expr MPType -> Expr MPType
uncurryFunction [(name, annot)] mt e    = 
  Function name annot e Nothing
uncurryFunction ((name, annot):as) mt e = 
  Function name annot (uncurryFunction as mt e) Nothing

}
