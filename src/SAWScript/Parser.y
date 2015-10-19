{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-tabs                #-}
module SAWScript.Parser
  ( parseModule
  , parseStmt
  , parseStmtSemi
  , parseSchema
  , ParseError(..)
  ) where

import Data.List
import qualified Data.Map as Map (fromList)
import SAWScript.Token
import SAWScript.Lexer
import SAWScript.AST
import SAWScript.Utils

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Utils.Ident as P (packIdent, packModName)

import qualified Text.Show.Pretty as PP

import Control.Applicative

}

%name parseModule Stmts
%name parseStmt Stmt
%name parseStmtSemi StmtSemi
%name parseSchema PolyType
%error { parseError }
%tokentype { Token Pos }
%monad { Either ParseError }

%token
  'import'       { TReserved _ "import"         }
  'and'          { TReserved _ "and"            }
  'as'           { TReserved _ "as"             }
  'hiding'       { TReserved _ "hiding"         }
  'let'          { TReserved _ "let"            }
  'rec'          { TReserved _ "rec"            }
  'in'           { TReserved _ "in"             }
  'do'           { TReserved _ "do"             }
  'if'           { TReserved _ "if"             }
  'then'         { TReserved _ "then"           }
  'else'         { TReserved _ "else"           }
  'CryptolSetup' { TReserved _ "CryptolSetup"   }
  'JavaSetup'    { TReserved _ "JavaSetup"      }
  'LLVMSetup'    { TReserved _ "LLVMSetup"      }
  'ProofScript'  { TReserved _ "ProofScript"    }
  'TopLevel'     { TReserved _ "TopLevel"       }
  'Bit'          { TReserved _ "Bit"            }
  'Int'          { TReserved _ "Int"            }
  'String'       { TReserved _ "String"         }
  'Term'         { TReserved _ "Term"           }
  'Type'         { TReserved _ "Type"           }
  'AIG'          { TReserved _ "AIG"            }
  ';'            { TPunct    _ ";"              }
  '['            { TPunct    _ "["              }
  ']'            { TPunct    _ "]"              }
  '('            { TPunct    _ "("              }
  ')'            { TPunct    _ ")"              }
  '{'            { TPunct    _ "{"              }
  '}'            { TPunct    _ "}"              }
  ':'            { TPunct    _ ":"              }
  ','            { TPunct    _ ","              }
  '.'            { TPunct    _ "."              }
  '\\'           { TPunct    _ "\\"             }
  '='            { TPunct    _ "="              }
  '->'           { TPunct    _ "->"             }
  '<-'           { TPunct    _ "<-"             }
  string         { TLit      _ $$               }
  code           { TCode     _ _                }
  ctype          { TCType    _ _                }
  num            { TNum      _ _ $$             }
  name           { TVar      _ _                }

%right 'else'
%left ':'
%left '['
%left '.'

%%

Stmts :: { [Stmt] }
 : termBy(Stmt, ';')                    { $1 }

StmtSemi :: { Stmt }
 : fst(Stmt, opt(';'))                  { $1 }

Import :: { Import }
 : string mbAs mbImportSpec             { Import (Left $1) $2 $3 }
 -- TODO: allow imports by module name instead of path

mbAs :: { Maybe P.ModName }
 : 'as' name                            { Just (P.packModName [tokStr $2]) }
 | {- empty -}                          { Nothing }

mbImportSpec :: { Maybe P.ImportSpec }
 : '(' list(name) ')'                   { Just $ P.Only   [ P.packIdent (tokStr n) | n <- $2 ] }
 | 'hiding' '(' list(name) ')'          { Just $ P.Hiding [ P.packIdent (tokStr n) | n <- $3 ] }
 | {- empty -}                          { Nothing }

Stmt :: { Stmt }
 : Expression                           { StmtBind Nothing Nothing Nothing $1   }
 | Arg '<-' Expression                  { StmtBind (Just (fst $1)) (snd $1) Nothing $3 }
 | 'rec' sepBy1(Declaration, 'and')     { StmtLet (Recursive $2)                  }
 | 'let' Declaration                    { StmtLet (NonRecursive $2)               }
 | 'let' Code                           { StmtCode $2                 }
 | 'import' Import                      { StmtImport $2               }

Declaration :: { Decl }
 : name list(Arg) '=' Expression        { Decl (toLName $1) Nothing (buildFunction $2 $4) }
 | name list(Arg) ':' Type '=' Expression
                                        { Decl (toLName $1) Nothing (buildFunction $2 (TSig $6 $4)) }

Arg :: { (LName, Maybe Type) }
 : name                                 { (toLName $1, Nothing) }
 | '(' name ':' Type ')'                { (toLName $2, Just $4) }

Expression :: { Expr }
 : IExpr                                { $1 }
 | IExpr ':' Type                       { TSig $1 $3          }
 | '\\' list1(Arg) '->' Expression      { buildFunction $2 $4 }
 | 'let' Declaration 'in' Expression    { Let (NonRecursive $2) $4 }
 | 'rec' sepBy1(Declaration, 'and')
   'in' Expression                      { Let (Recursive $2) $4 }

IExpr :: { Expr }
 : AExprs                               { $1 }

AExprs :: { Expr }
 : list1(AExpr)                         { buildApplication $1 }

AExpr :: { Expr }
 : '(' ')'                              { Tuple []                }
 | '[' ']'                              { Array []                }
 | string                               { String $1               }
 | Code                                 { Code $1                 }
 | CType                                { CType $1                }
 | num                                  { Z $1                    }
 | name                                 { Var (Located (tokStr $1) (tokStr $1) (tokPos $1)) }
 | '(' Expression ')'                   { $2                      }
 | '(' commas2(Expression) ')'          { Tuple $2                }
 | '[' commas(Expression) ']'           { Array $2                }
 | '{' commas(Field) '}'                { Record (Map.fromList $2) }
 | 'do' '{' termBy(Stmt, ';') '}'       { Block $3                }
 | AExpr '.' name                       { Lookup $1 (tokStr $3)   }
 | AExpr '.' num                        { TLookup $1 $3           }

Code :: { Located String }
 : code                                 { Located (tokStr $1) (tokStr $1) (tokPos $1) }

CType :: { Located String }
 : ctype                                { Located (tokStr $1) (tokStr $1) (tokPos $1) }

Field :: { (Name, Expr) }
 : name '=' Expression                  { (tokStr $1, $3) }

Names :: { [Name] }
 : name                                 { [tokStr $1] }
 | name ',' Names                       { tokStr $1:$3 }

PolyType :: { Schema }
 : Type                                 { tMono $1                }
 | '{' Names '}' Type                   { Forall $2 $4            }

Type :: { Type }
 : BaseType                             { $1                      }
 | BaseType '->' Type                   { tFun $1 $3              }

FieldType :: { Bind Type }
  : name ':' BaseType                   { (tokStr $1, $3)         }

BaseType :: { Type }
 : name                                 { tVar (tokStr $1)        }
 | Context BaseType                     { tBlock $1 $2            }
 | '(' ')'                              { tTuple []               }
 | 'Bit'                                { tBool                   }
 | 'Int'                                { tZ                      }
 | 'String'                             { tString                 }
 | 'Term'                               { tTerm                   }
 | 'Type'                               { tType                   }
 | 'AIG'                                { tAIG                    }
 | '(' Type ')'                         { $2                      }
 | '(' commas2(Type) ')'                { tTuple $2               }
 | '[' Type ']'                         { tArray $2               }
 | '{' commas(FieldType) '}'            { tRecord $2              }

Context :: { Type }
 : 'CryptolSetup'                       { tContext CryptolSetup   }
 | 'JavaSetup'                          { tContext JavaSetup      }
 | 'LLVMSetup'                          { tContext LLVMSetup      }
 | 'ProofScript'                        { tContext ProofScript    }
 | 'TopLevel'                           { tContext TopLevel       }
 | name                                 { tVar (tokStr $1)        }

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

sepBy2(p, q) : p q sepBy1(p, q) { $1 : $3 }

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

commas(p) : sepBy1(p, ',') { $1 }
commas2(p) : sepBy2(p, ',') { $1 }

{

data ParseError
  = UnexpectedEOF
  | UnexpectedToken (Token Pos)

instance Show ParseError where
  show e =
    case e of
      UnexpectedEOF     -> "Parse error: unexpected end of file"
      UnexpectedToken t -> "Parse error at line " ++ show ln ++ ", col " ++ show col
        where Pos _ ln col = tokPos t

parseError :: [Token Pos] -> Either ParseError b
parseError toks = case toks of
  []    -> Left UnexpectedEOF
  t : _ -> Left (UnexpectedToken t)

buildFunction :: [(LName, Maybe Type)] -> Expr -> Expr
buildFunction args e = foldr foldFunction e args
  where
  foldFunction (argName, mType) rhs = Function argName mType rhs

buildApplication :: [Expr] -> Expr
buildApplication = foldl1 (\e body -> Application e body)

}
