module SAWScript.AST where 

import Data.Foldable

type Name = String
type Args = [(Name, Maybe TypeAnnotation)]
type Label = Maybe Name

type Bits = [Bool]

type TypeAnnotation = Maybe String

data Pattern
  = Literal Bits 
--  | Wildcard     
--  | Concat        deriving Eq



data ArrowType
  = Let
  | Fun
  | Inj
  | Sur
  | Iso deriving Eq

data Expr a
  = Var Name                          a
  | Pattern Pattern                   a
  | Func ArrowType Args (Expr a)      a
  | App (Expr a) (Expr a)             a
  | Switch (Expr a) [(Expr a,Expr a)] a
  | DM [(Maybe Name, Expr a)]         a deriving (Eq)