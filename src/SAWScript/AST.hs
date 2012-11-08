module SAWScript.AST where

import Data.List
import Text.PrettyPrint.HughesPJ

type Name = String

data Statement a
  = Declarations [Declaration a]
  | ForwardDecl Name Type
  | Command (Expr a)
  | Typedef Name Type
  | Import Name (Maybe [Name]) (Maybe Name) deriving Show

data Declaration a
  = Declaration Name [(Name, a)] (Expr a) a deriving Show

data Expr a
  = Bitfield    [Bool]                   a
  | Quote       String                   a
  | Z           Integer                  a
  | Var         Name                     a
  | Record      [(Name, Expr a)]         a
  | Function    [(Name, a)] (Expr a)     a
  | Application (Expr a)    (Expr a)     a
  | Array       [Expr a]                 a
  | Procedure   [Statement a]            a
  | Lookup      (Expr a)    Name         a
  | Index       (Expr a)    (Expr a)     a
  | LetBlock    [Declaration a] (Expr a) deriving Show
--  | Tuple       [Expr a]          a

data Type 
  = Z'
  | Procedure'
  | Bitfield'  Integer
  | Var'       String
  | Function'  [Type] Type
  | Array'     Type   (Maybe Integer)
  | Record'    [(Name, Type)] deriving Show
--  | Tuple'     [Type]

