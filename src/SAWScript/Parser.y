{
{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : lerkok
-}

{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module SAWScript.Parser(parseSAW) where

import SAWScript.MethodAST
import SAWScript.Token
import SAWScript.Utils hiding (Blif, Verify)
import {-# SOURCE #-} SAWScript.ParserActions
}

%expect 0
%tokentype { Token Pos }
%monad { Parser }
%lexer { lexer } { TEOF _ _ }
%error { parseError }
%name parseSAW SAWScript

%token
   'import'       { TReserved _ "import"       }
   'extern'       { TReserved _ "extern"       }
   'let'          { TReserved _ "let"          }
   'SBV'          { TReserved _ "SBV"          }
   'Bit'          { TReserved _ "Bit"          }
   'pragma'       { TReserved _ "pragma"       }
   'method'       { TReserved _ "method"       }
   'rule'         { TReserved _ "rule"         }
   'from'         { TReserved _ "from"         }
   'pc'           { TReserved _ "pc"           }
   'line'         { TReserved _ "line"         }
   'mayAlias'     { TReserved _ "mayAlias"     }
   'assert'       { TReserved _ "assert"       }
   'ensure'       { TReserved _ "ensure"       }
   'modify'       { TReserved _ "modify"       }
   'return'       { TReserved _ "return"       }
   'blif'         { TReserved _ "blif"         }
   'quickcheck'   { TReserved _ "quickcheck"   }
   'verify'       { TReserved _ "verify"       }
   'enable'       { TReserved _ "enable"       }
   'disable'      { TReserved _ "disable"      }
   'auto'         { TReserved _ "auto"         }
   'set'          { TReserved _ "set"          }
   'verification' { TReserved _ "verification" }
   'on'           { TReserved _ "on"           }
   'off'          { TReserved _ "off"          }
   'var'          { TReserved _ "var"          }
   'args'         { TReserved _ "args"         }
   'locals'       { TReserved _ "locals"       }
   'this'         { TReserved _ "this"         }
   -- Java types
   'boolean'      { TReserved _ "boolean"      }
   'byte'         { TReserved _ "byte"         }
   'char'         { TReserved _ "char"         }
   'double'       { TReserved _ "double"       }
   'float'        { TReserved _ "float"        }
   'int'          { TReserved _ "int"          }
   'long'         { TReserved _ "long"         }
   'short'        { TReserved _ "short"        }
   'true'         { TReserved _ "true"         }
   'false'        { TReserved _ "false"        }
   'forAll'       { TReserved _ "forAll"       }
   'if'           { TReserved _ "if"           }
   'then'         { TReserved _ "then"         }
   'else'         { TReserved _ "else"         }
   'abc'          { TReserved _ "abc"          }
   'rewrite'      { TReserved _ "rewrite"      }
   'smtlib'       { TReserved _ "smtlib"       }
   'yices'        { TReserved _ "yices"        }
   'expand'       { TReserved _ "expand"       }
   var            { TVar      _ _              }
   str            { TLit      _ $$             }
   num            { TNum      _ _ _            }
   ';'            { TPunct    _ ";"            }
   '['            { TPunct    _ "["            }
   ']'            { TPunct    _ "]"            }
   '('            { TPunct    _ "("            }
   ')'            { TPunct    _ ")"            }
   '{'            { TPunct    _ "{"            }
   '}'            { TPunct    _ "}"            }
   ':'            { TPunct    _ ":"            }
   '::'           { TPunct    _ "::"           }
   ','            { TPunct    _ ","            }
   '.'            { TPunct    _ "."            }
   '='            { TPunct    _ "="            }
   '->'           { TPunct    _ "->"           }
   ':='           { TPunct    _ ":="           }
   '<|'           { TPunct    _ "<|"           }
   '|>'           { TPunct    _ "|>"           }
   'not'          { TOp       _ "not"          }
   '~'            { TOp       _ "~"            }
   '-'            { TOp       _ "-"            }
   '*'            { TOp       _ "*"            }
   '+'            { TOp       _ "+"            }
   '/s'           { TOp       _ "/s"           }
   '%s'           { TOp       _ "%s"           }
   '<<'           { TOp       _ "<<"           }
   '>>s'          { TOp       _ ">>s"          }
   '>>u'          { TOp       _ ">>u"          }
   '&'            { TOp       _ "&"            }
   '^'            { TOp       _ "^"            }
   '|'            { TOp       _ "|"            }
   '#'            { TOp       _ "#"            }
   '=='           { TOp       _ "=="           }
   '!='           { TOp       _ "!="           }
   '>=s'          { TOp       _ ">=s"          }
   '>=u'          { TOp       _ ">=u"          }
   '>s'           { TOp       _ ">s"           }
   '>u'           { TOp       _ ">u"           }
   '<=s'          { TOp       _ "<=s"          }
   '<=u'          { TOp       _ "<=u"          }
   '<s'           { TOp       _ "<s"           }
   '<u'           { TOp       _ "<u"           }
   '&&'           { TOp       _ "&&"           }
   '||'           { TOp       _ "||"           }
   '==>'          { TOp       _ "==>"          }

-- Operators, precedence increases as you go down in this list
%nonassoc MIN
%right 'else'
%right '==>'
%left '||'
%left '&&'
%nonassoc '>=s' '>=u' '>s' '>u' '<=s' '<=u' '<s' '<u'
%nonassoc '==' '!='
%right '#'
%left '|'
%left '^'
%left '&'
%left '<<' '>>s' '>>u'
%left '+' '-'
%left '*' '/s' '%s'
%left ':'
%left '['
%left '.'
%right NEG 'not' '~'
%%

-- SAWScript
SAWScript :: { [Input SAWScriptCommand] }
SAWScript : termBy(SAWScriptCommand, ';') { $1 }

-- Verifier commands
SAWScriptCommand :: { Input SAWScriptCommand }
SAWScriptCommand
  : 'import' str                     { inp $1 (ImportCommand $2)}
  | 'extern' 'SBV' var '(' str ')' ':' FnType 
                                     { inp $1 (ExternSBV (tokStr $3) $5 $8) }
  | 'let' var '=' Expr               { inp $1 (GlobalLet (tokStr $2) $4)    }
  | 'let' var '(' sepBy1(VarBinding, ',') ')' ':' ExprType '=' Expr
                                     { inp $1 (GlobalFn (tokStr $2) $4 $7 $9)  }
  | 'pragma' var ':' 'SBV' str       { inp $1 (SBVPragma (tokStr $2) $5)    }
  | 'set' 'verification' 'on'        { inp $1 (SetVerification True)  }
  | 'set' 'verification' 'off'       { inp $1 (SetVerification False) }
  | 'method' Qvar '{' seplist(MethodSpecDecl, ';') '}' 
                                     { inp $1 (DeclareMethodSpec (snd $2) $4) }
  | 'rule' var ':' RuleParams Expr '->' Expr 
                                     { inp $1 (Rule (tokStr $2) $4 $5 $7) }
  | 'enable'  var                    { inp $1 (Enable  (tokStr $2)) }
  | 'disable' var                    { inp $1 (Disable (tokStr $2)) }

-- Types
FnType  :: { FnType }
FnType  :     ExprType      '->' ExprType  { FnType [$1] $3 }
        | '(' ExprTypes ')' '->' ExprType  { FnType $2 $5   }

-- Comma separated types, at least one
ExprTypes :: { [ExprType] }
ExprTypes : sepBy1(ExprType, ',') { $1 }

ExprType :: { ExprType }
ExprType
   : 'Bit'                           {  BitType    (tokPos $1)             }
   | '[' ExprWidth ']' %prec '#' { BitvectorType (tokPos $1) $2          }
   | '[' ExprWidth ']' ExprType  { Array         (tokPos $1) $2 $4       }
   | '{' RecordFTypes '}'            {% mkRecordT  (tokPos $1) $2          }
   | var                             {  ShapeVar   (tokPos $1) (tokStr $1) }

ExprWidth :: { ExprWidth }
ExprWidth : int                     { WidthConst (fst $1) (snd $1)       }
          | var                     { WidthVar   (tokPos $1) (tokStr $1) }
          | ExprWidth '+' ExprWidth { WidthAdd   (tokPos $2) $1 $3       }

VarBinding :: { Input VarBinding }
VarBinding : var ':' ExprType { inp $1 (tokStr $1, $3) }

-- Rule parameters
RuleParams :: { [Input (String, ExprType)] }
RuleParams : {- empty -}                              { [] }
           | 'forAll' '{' sepBy1(VarBinding, ',')  '}' '.' { $3 }


-- Comma separated expressions, potentially none
Exprs :: { [Expr] }
Exprs : sepBy(Expr, ',') { $1 }

-- Comma separated sequence of expressions, at least one
Exprs1 :: { [Expr] }
Exprs1 : sepBy1(Expr, ',') { $1 }

-- Expressions
Expr :: { Expr }
Expr : var                             { Var (tokPos $1) (tokStr $1) }
     | 'true'                          { ConstantBool (tokPos $1) True }
     | 'false'                         { ConstantBool (tokPos $1) False }
     | num                             { ConstantInt (tokPos $1) (tokNum $1) }
     | '<|' poly '|>'                  { ConstantInt  (tokPos $1) $2 }
     | '{' RecordFlds '}'              {% mkRecordV   (tokPos $1) $2 }
     | Expr ':' ExprType               { TypeExpr     (tokPos $2) $1 $3 }
     | Expr '.' var                    { DerefField (tokPos $2) $1 (tokStr $3) }
     | var '(' Exprs ')'               { ApplyExpr (tokPos $1) (tokStr $1) $3 }
     | Expr '[' Expr ']'               { GetArray     (tokPos $2) $1 $3 }
     | '[' Exprs ']'                   { MkArray      (tokPos $1) $2 }
     | '~' Expr                        { BitComplExpr (tokPos $1) $2 }
     | 'not' Expr                      { NotExpr      (tokPos $1) $2 }
     | '-' Expr %prec NEG              { NegExpr      (tokPos $1) $2 }
     | Expr '*'   Expr                 { MulExpr      (tokPos $2) $1 $3 }
     | Expr '/s'  Expr                 { SDivExpr     (tokPos $2) $1 $3 }
     | Expr '%s'  Expr                 { SRemExpr     (tokPos $2) $1 $3 }
     | Expr '+'   Expr                 { PlusExpr     (tokPos $2) $1 $3 }
     | Expr '-'   Expr                 { SubExpr      (tokPos $2) $1 $3 }
     | Expr '<<'  Expr                 { ShlExpr      (tokPos $2) $1 $3 }
     | Expr '>>s' Expr                 { SShrExpr     (tokPos $2) $1 $3 }
     | Expr '>>u' Expr                 { UShrExpr     (tokPos $2) $1 $3 }
     | Expr '&'   Expr                 { BitAndExpr   (tokPos $2) $1 $3 }
     | Expr '^'   Expr                 { BitXorExpr   (tokPos $2) $1 $3 }
     | Expr '|'   Expr                 { BitOrExpr    (tokPos $2) $1 $3 }
     | Expr '#'   Expr                 { AppendExpr   (tokPos $2) $1 $3 }
     | Expr '=='  Expr                 { EqExpr       (tokPos $2) $1 $3 }
     | Expr '!='  Expr                 { IneqExpr     (tokPos $2) $1 $3 }
     | Expr '>=s' Expr                 { SGeqExpr     (tokPos $2) $1 $3 }
     | Expr '>=u' Expr                 { UGeqExpr     (tokPos $2) $1 $3 }
     | Expr '>s'  Expr                 { SGtExpr      (tokPos $2) $1 $3 }
     | Expr '>u'  Expr                 { UGtExpr      (tokPos $2) $1 $3 }
     | Expr '<=s' Expr                 { SLeqExpr     (tokPos $2) $1 $3 }
     | Expr '<=u' Expr                 { ULeqExpr     (tokPos $2) $1 $3 }
     | Expr '<s'  Expr                 { SLtExpr      (tokPos $2) $1 $3 }
     | Expr '<u'  Expr                 { ULtExpr      (tokPos $2) $1 $3 }
     | Expr '&&'  Expr                 { AndExpr      (tokPos $2) $1 $3 }
     | Expr '||'  Expr                 { OrExpr       (tokPos $2) $1 $3 }
     | Expr '==>' Expr                 { ImpExpr      (tokPos $2) $1 $3 }
     | 'this'                          { ThisExpr     (tokPos $1)       }
     | 'args' '[' int ']'              { ArgExpr      (tokPos $1) (snd $3)}
     | 'locals' '[' num ']'            { LocalExpr    (tokPos $1) (tokNum $3) }
     | '(' Expr ')'                    { $2 }
     | 'if' Expr 'then' Expr 
                 'else' Expr           { IteExpr (tokPos $1) $2 $4 $6 }

-- Records
RecordFTypes :: { [(Pos, String, ExprType)] }
RecordFTypes : sepBy(connected(var, ':', ExprType), ';')
                               { map ((\(v, e) -> (tokPos v, tokStr v, e))) $1 }

RecordFlds :: { [(Pos, String, Expr)] }
RecordFlds : sepBy(connected(var, '=', Expr), ';')
                               { map ((\(v, e) -> (tokPos v, tokStr v, e))) $1 }

MethodLocation :: { MethodLocation }
MethodLocation
  : 'pc' num       { PC (tokNum $2) }
  | 'line' '+' num { LineOffset (tokNum $3) }
  | 'line' '=' num { LineExact (tokNum $3) }

MethodSpecDecl :: { MethodSpecDecl }
MethodSpecDecl
  : LSpecDecl            { Behavior $1 }
  | 'from' MethodLocation LSpecDecl
                         { SpecAt (tokPos $1) $2 $3 }
  | 'quickcheck' num opt(num) ';'
                         { SpecPlan (tokPos $1)
                                    (QuickCheck (tokNum $2) (fmap tokNum $3)) }
  | 'blif' opt(str) ';'  { SpecPlan (tokPos $1) (Blif $2) }
  | 'verify' VerifyCommand
                         { SpecPlan (tokPos $1) (Verify $2) }

LSpecDecl :: { BehaviorDecl }
LSpecDecl 
  : '{' seplist(LSpecDecl, ';') '}' { Block $2 }
  | LSpecStatement ';' { $1 }
  | 'if' '(' Expr ')' LSpecDecl %prec MIN { MethodIf (tokPos $1) $3 $5    }
  | 'if' '(' Expr ')' LSpecDecl
               'else' LSpecDecl { MethodIfElse (tokPos $1) $3 $5 $7       }

LSpecStatement :: { BehaviorDecl }
LSpecStatement
  : 'var' Exprs1 '::' JavaType   { VarDecl      (tokPos $1) $2 $4          }
  | 'mayAlias' '{' Exprs1 '}'    { MayAlias     (tokPos $1) $3             }
  | 'let' var '=' Expr           { MethodLet    (tokPos $1) (tokStr $2) $4 }
  | 'assert' Expr                { AssertPred   (tokPos $1) $2             }
  | 'assert' Expr ':=' Expr      { AssertImp    (tokPos $1) $2 $4          }
  | 'ensure' Expr ':=' Expr      { EnsureImp    (tokPos $1) $2 $4          }
  | 'modify' Exprs1              { Modify       (tokPos $1) $2             }
  | 'return' Expr                { Return       (tokPos $1) $2             }

JavaType :: { JavaType }
JavaType : 'boolean'            { BoolType (tokPos $1)      }
         | 'byte'               { ByteType (tokPos $1)      }
         | 'char'               { CharType (tokPos $1)      }
         | 'int'                { IntType (tokPos $1)       }
         | 'long'               { LongType (tokPos $1)      }
         | 'short'              { ShortType (tokPos $1)     }
         | 'float'              { FloatType (tokPos $1)     }
         | 'double'             { DoubleType (tokPos $1)    }
         | JavaType '[' int ']' { ArrayType $1 (snd $3)     }
         | Qvar                 { RefType (fst $1) (snd $1) }

VerifyCommand :: { VerifyCommand }
VerifyCommand
  : 'from' MethodLocation VerifyCommand { VerifyAt (tokPos $1) $2 $3 }
  | '{' list(VerifyCommand) '}'         { VerifyBlock $2 }
  | VerifyStatement ';'                 { $1 }

VerifyStatement :: { VerifyCommand }
  : 'rewrite'                          { Rewrite }
  | 'abc'                              { ABC }
  | 'smtlib' opt(int) opt(str)         { SmtLib (fmap snd $2) $3 }
  | 'yices'  opt(int)                  { Yices (fmap snd $2) }
  | 'expand' Expr                      { Expand $2 }
  | 'enable'  var                      { VerifyEnable  (tokPos $2) (tokStr $2) }
  | 'disable' var                      { VerifyDisable (tokPos $2) (tokStr $2) }

-- A qualified variable
Qvar :: { (Pos, [String]) }
Qvar : sepBy1(var, '.') { (head (map tokPos $1), map tokStr $1) }

-- A literal that must fit into a Haskell Int
int :: { (Pos, Int) }
int : num  {% parseIntRange (tokPos $1) (0, maxBound) (tokNum $1) }

-- Polynomials, another way of writing Integers
poly :: { Integer }
poly : poly '+' polyTerm  { $1 + $3 }
     | poly '-' polyTerm  { $1 - $3 }
     | '-' polyTerm       { - $2    }
     | polyTerm           { $1      }

polyTerm :: { Integer }
polyTerm :     num '^' num   {             tokNum $1 ^ tokNum $3   }
         | num num           { tokNum $1 * tokNum $2               }
         | num num '^' num   { tokNum $1 * (tokNum $2 ^ tokNum $4) }
         | num               { tokNum $1                           }

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
