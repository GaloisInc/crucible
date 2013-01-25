{

module SAWScript.Parser ( parse ) where

import Data.List
import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.Compiler
import SAWScript.AST
import SAWScript.Unify
import SAWScript.Lexer
import Control.Applicative

}

%name parse
%error { parseError }
%tokentype { T.Token AlexPosn }
%monad { Err } { (>>=) } { return }

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
 | name '::' Type                       { TopTypeDecl $1 $3 }
 | 'type' name '=' Type                 { TypeDef $2 $4     }
 | 'import' Import                      { $2                }

BlockStatement :: { BlockStmt MPType }
 : Expression                           { Bind Nothing Context $1   }
 | name '=' Expression                  { Bind (Just $1) Context $3 }
 | name '::' Type                       { BlockTypeDecl $1 $3       }
 | 'let' Declarations1                  { BlockLet $2               }

Declaration :: { (Name, Expr MPType) }
 : name Args '=' Expression             { ($1, buildFunction $2 $4)                              }
 | name Args ':' Type '=' Expression    { ($1, updateAnnotation (buildFunction $2 $6) (Just $4)) }

Import :: { TopStmt MPType }
 : name                                 { Import $1 Nothing Nothing       }
 | name '(' CommaSepNames ')'           { Import $1 (Just $3) Nothing     }
 | name 'as' name                       { Import $1 Nothing (Just $3)     }
 | name '(' CommaSepNames ')' 'as' name { Import $1 (Just $3) (Just $6)   }

Arg :: { (Name, MPType) }
 : name                                 { ($1, Nothing) }
 | '(' name ':' Type ')'                { ($2, Just $4) }

Expression :: { Expr MPType }
 : Expressions                          { buildApplication $1 }

Expressions :: { [Expr MPType] }
 : ExpressionPrimitive                  { [$1]  }
 | SafeExpression Expressions           { $1:$2 }

ExpressionPrimitive :: { Expr MPType }
 : NakedExpression                      { $1 }
 | SafeExpression                       { $1 }

NakedExpression :: { Expr MPType }
 : 'fun' Args1 '->' Expression          { buildFunction $2 $4           }
 | 'let' Declarations1 'in' Expression  { LetBlock $2 $4                }
 | SafeExpression infixOp Expression                    
    { Application (Application (Var $2 Nothing ) $1 Nothing) $3 Nothing }

SafeExpression :: { Expr MPType }
 : unit   MaybeType                            { Unit $2                       }
 | bits   MaybeType                            { Array (bitsOfString $1) $2    }
 | string MaybeType                            { Quote $1 $2                   }
 | int    MaybeType                            { Z (read $1) $2                }
 | name   MaybeType                            { Var $1 $2                     }
 | '(' Expressions ')' MaybeType               { updateAnnotation (buildApplication $2) $4 }
 | ' [' CommaSepExprs ']' MaybeType            { Array $2 $4                   }
 | '{' CommaSepFields '}' MaybeType            { Record $2 $4                  }
 | 'do' '{' SemiSepBlockStmts '}' MaybeType    { Block $3 $5                   }
 | SafeExpression '.' name MaybeType           { Lookup $1 $3 $4               }
 | SafeExpression '[' Expression ']' MaybeType { Index $1 $3 $5                }

Field :: { (Name, Expr MPType) }
 : name ':' Expression                  { ($1, $3) }
 | string ':' Expression                { ($1, $3) }

MaybeType :: { MPType }
 : {- Nothing -}                        { Nothing }
 | ':' Type                             { Just $2 }

Type :: { PType }
 : BaseType                             { $1 }
 | BaseType '->' Type                   { function $1 $3 }

BaseType :: { PType }
 : 'integer'                            { z                       }
 | 'string'                             { quote                   } 
 | 'bit'                                { bit                     }
 | name                                 { syn $1                  }
 | '(' TupledTypes ')'                  { $2                      }
 | LeftBracket int ']'                  { array bit (i $ read $2) }
 | LeftBracket int ']' BaseType         { array $4  (i $ read $2) }

TupledTypes :: { PType }
 : {- Nothing -}                        { unit }
 | CommaSepTypes1                       { if length $1 == 1 then head $1 else tuple $1 }

CommaSepTypes1 :: { [PType] } 
 : Type                                 { $1:[] }
 | Type ',' CommaSepTypes1             { $1:$3 }

Declarations1 :: { [(Name, Expr MPType)] }
 : Declaration                          { $1:[] }
 | Declaration 'and' Declarations1      { $1:$3 }

Args :: { [(Name, MPType)] }
 : {- Nothing -}                        { [] }
 | Args1                                { $1 }

Args1 :: { [(Name, MPType)] }
 : Arg                                  { $1:[] }
 | Arg Args1                            { $1:$2 }

SemiSepBlockStmts :: { [BlockStmt MPType] }
 : {- Nothing -}                        { []    }
 | BlockStatement ';' SemiSepBlockStmts { $1:$3 }

CommaSepExprs :: { [Expr MPType] }
 : {- Nothing -}                        { [] }
 | CommaSepExprs1                       { $1 }

CommaSepExprs1 :: { [Expr MPType] }
 : Expression                           { $1:[] }
 | Expression ',' CommaSepExprs1        { $1:$3 }

CommaSepFields :: { [(Name, Expr MPType)] }
 : {- Nothing -}                        { [] }
 | CommaSepFields1                      { $1 }

CommaSepFields1 :: { [(Name, Expr MPType)] }
 : Field                                { $1:[] }
 | Field ',' CommaSepFields1            { $1:$3 }

CommaSepNames :: { [Name] }
  : {- Nothing -}                       { [] }
  | CommaSepNames1                      { $1 }

CommaSepNames1 :: { [Name] }
  : name                                { $1:[] }
  | name ',' CommaSepNames1             { $1:$3 }

LeftBracket :: { () }
 :  '[' { () }
 | ' [' { () }

{

parseError :: [T.Token AlexPosn] -> Err b
parseError toks = case toks of
  []  -> fail "Parse error, but where?"
  t:_ -> fail ("Parse error at line " ++ show ln ++ ", col " ++ show col)
    where
    AlexPn _ ln col = T.tokPos t

bitsOfString :: String -> [Expr MPType]
bitsOfString = map ((flip Bit $ Just bit) . (/= '0'))

buildFunction :: [(Name, MPType)] -> Expr MPType -> Expr MPType 
buildFunction args e = foldr foldFunction e args
  where
  foldFunction (argName,mType) rhs = Function argName mType e $
    function <$> mType <*> decor rhs

buildApplication :: [Expr MPType] -> Expr (MPType)
buildApplication [e]    = e
buildApplication (e:es) = Application e app' $
  function <$> decor e <*> decor app'
  where
  app' = buildApplication es

buildType :: [PType] -> PType
buildType [t]    = t
buildType (t:ts) = function t (buildType ts)

}

