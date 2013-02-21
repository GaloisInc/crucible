{

module SAWScript.Parser ( parse ) where

import Data.List
import SAWScript.Token
import SAWScript.Lexer
import SAWScript.Compiler
import SAWScript.AST
import SAWScript.Unify
import SAWScript.Lexer

import qualified Text.Show.Pretty as PP

import Control.Applicative

}

%name parse TopStatements
%error { parseError }
%tokentype { Token AlexPosn }
%monad { Err } { (>>=) } { return }

%token
'import'                                { Token Keyword    _ "import"  }
'and'                                   { Token Keyword    _ "and"     }
'as'                                    { Token Keyword    _ "as"      }
'let'                                   { Token Keyword    _ "let"     }
'fun'                                   { Token Keyword    _ "fun"     }
'in'                                    { Token Keyword    _ "in"      }
'type'                                  { Token Keyword    _ "type"    }
'do'                                    { Token Keyword    _ "do"      }
'='                                     { Token Infix      _ "="       }
'->'                                    { Token Infix      _ "->"      }
';'                                     { Token Infix      _ ";"       }
','                                     { Token Infix      _ ","       }
':'                                     { Token Infix      _ ":"       }
'::'                                    { Token Infix      _ "::"      }
'('                                     { Token OutfixL    _ "("       }
')'                                     { Token OutfixR    _ ")"       }
']'                                     { Token OutfixR    _ "]"       }
'{'                                     { Token OutfixL    _ "{"       }
'}'                                     { Token OutfixR    _ "}"       }
'['                                     { Token OutfixL    _ "["       }
'.'                                     { Token Postfix    _ "."       }
infixOp                                 { Token Infix      _ $$        }
bits                                    { Token BitLiteral _ $$        }
string                                  { Token String     _ $$        }
int                                     { Token Integer    _ $$        }
name                                    { Token Identifier _ $$        }

%%

TopStatements :: { [TopStmt MPType] }
 : {- Nothing -}                  { []    }
 | TopStatement ';' TopStatements { $1:$3 }

TopStatement :: { TopStmt MPType }
 : 'let' Declarations1                  { TopLet $2         }
 | name ':' PolyType                    { TopTypeDecl $1 $3 }
 | 'type' name '=' Type                 { TypeDef $2 $4     }
 | 'import' Import                      { $2                }

-- TODO: allow other contexts to be used.
BlockStmt :: { BlockStmt MPType }
 : Expression                           { Bind Nothing TopLevelContext $1   }
 | name '=' Expression                  { Bind (Just $1) TopLevelContext $3 }
 | name ':' PolyType                    { BlockTypeDecl $1 $3       }
 | 'let' Declarations1                  { BlockLet $2               }

Declaration :: { (Name, Expr MPType) }
 : name Args '=' Expression             { ($1, buildFunction $2 $4)       }

Import :: { TopStmt MPType }
 : name                                 { Import $1 Nothing Nothing       }
 | name '(' sepBy(name, ',') ')'        { Import $1 (Just $3) Nothing     }
 | name 'as' name                       { Import $1 Nothing (Just $3)     }
 | name '(' sepBy(name, ',') ')' 'as' name { Import $1 (Just $3) (Just $6)   }

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
 : '(' ')'                              { Unit Nothing                    }
 | bits                                 { Array (bitsOfString $1) Nothing }
 | string                               { Quote $1 Nothing                }
 | int                                  { Z (read $1) Nothing             }
 | name                                 { Var $1 Nothing                  }
 | '(' Expressions ')'                  { buildApplication $2             }
 | '[' CommaSepExprs ']'                { Array $2 Nothing                }
 | '{' CommaSepFields '}'               { Record $2 Nothing               }
 | 'do' '{' sepBy(BlockStmt, ';') '}'   { Block $3 Nothing                }
 | SafeExpression '.' name              { Lookup $1 $3 Nothing            }
 | SafeExpression ':' Type              { updateAnnotation $1 (Just $3)   }

Field :: { (Name, Expr MPType) }
 : name '=' Expression                  { ($1, $3) }

MaybeType :: { MPType }
 : {- Nothing -}                        { Nothing }
 | ':' Type                             { Just $2 }

Names :: { [Name] } 
 : name                                 { [$1] }
 | name ',' Names                       { $1:$3 }

PolyType :: { PType }
 : '{' Names '}' Type                   { synToPoly $2 $4         }
 | Type                                 { $1                      }

Type :: { PType }
 : BaseType                             { $1 }
 | BaseType '->' Type                   { function $1 $3 }

BaseType :: { PType }
 : name                                 { syn $1                  }
 | '(' TupledTypes ')'                  { $2                      }
 | '[' int ']'                          { array bit (i $ read $2) }
 | '[' int ']' BaseType                 { array $4  (i $ read $2) }

TupledTypes :: { PType }
 : {- Nothing -}                        { unit }
 | CommaSepTypes1                       { if length $1 == 1 then head $1 else tuple $1 }

CommaSepTypes1 :: { [PType] } 
 : Type                                 { [$1] }
 | Type ',' CommaSepTypes1              { $1:$3 }

Declarations1 :: { [(Name, Expr MPType)] }
 : Declaration                          { [$1] }
 | Declaration 'and' Declarations1      { $1:$3 }

Args :: { [(Name, MPType)] }
 : {- Nothing -}                        { [] }
 | Args1                                { $1 }

Args1 :: { [(Name, MPType)] }
 : Arg                                  { [$1] }
 | Arg Args1                            { $1:$2 }

{-
SemiSepBlockStmts :: { [BlockStmt MPType] }
 : {- Nothing -}                        { []    }
 | BlockStmt ';' SemiSepBlockStmts { $1:$3 }
-}

CommaSepExprs :: { [Expr MPType] }
 : {- Nothing -}                        { [] }
 | CommaSepExprs1                       { $1 }

CommaSepExprs1 :: { [Expr MPType] }
 : Expression                           { [$1] }
 | Expression ',' CommaSepExprs1        { $1:$3 }

CommaSepFields :: { [(Name, Expr MPType)] }
 : {- Nothing -}                        { [] }
 | CommaSepFields1                      { $1 }

CommaSepFields1 :: { [(Name, Expr MPType)] }
 : Field                                { [$1] }
 | Field ',' CommaSepFields1            { $1:$3 }

-- Parameterized productions, most come directly from the Happy manual.
fst(p, q)  : p q   { $1 }
snd(p, q)  : p q   { $2 }
both(p, q) : p q   { ($1, $2) }

-- p bracketed with some delims o-c
bracketed(o, p, c) : o p c { $2 }

-- p and q, connected by some connective c
connected(p, c, q) : p c q { ($1, $3) }

-- an optional p
opt(p) : p            { Just $1 }
       | {- empty -}  { Nothing }

-- A reversed list of at least 1 p's
rev_list1(p) : p              { [$1]    }
             | rev_list1(p) p { $2 : $1 }

-- A list of at least 1 p's
list1(p) : rev_list1(p)   { reverse $1 }

-- A potentially empty list of p's
list(p) : {- empty -}    { [] }
        | list1(p)       { $1 }

-- A reversed list of at least 1 p's
seprev_list(p,q) : seprev_list(p,q) p { $2 : $1 }
                 | seprev_list(p,q) q { $1 }
                 | {- empty -}    { [] }

-- A potentially empty list of p's separated by zero or more qs (which are ignored).
seplist(p,q) : seprev_list(p,q)  { reverse $1 }

-- A list of at least one 1 p's, separated by q's
sepBy1(p, q) : p list(snd(q, p)) { $1 : $2 }

-- A list of 0 or more p's, separated by q's
sepBy(p, q) : {- empty -}  { [] }
            | sepBy1(p, q) { $1 }

-- A list of at least one 1 p's, terminated by q's
termBy1(p, q) : list1(fst(p, q)) { $1 }

-- A list of 0 or more p's, terminated by q's
termBy(p, q) : {- empty -}    { [] }
             | termBy1(p, q)  { $1 }

-- one or the other
either(p, q) : p  { Left  $1 }
             | q  { Right $1 }

{

parseError :: [Token AlexPosn] -> Err b
parseError toks = case toks of
  []  -> parseFail "Parse error, but where?"
  t:_ -> parseFail ("Parse error at line " ++ show ln ++ ", col " ++ show col)
    where
    AlexPn _ ln col = tokPos t
  where
  parseFail :: String -> Err b
  parseFail = fail . (++ "\n" ++ PP.ppShow toks)

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

