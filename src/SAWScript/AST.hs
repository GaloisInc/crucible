module SAWScript.AST where 

import Data.Foldable
import Data.Traversable
import Control.Applicative
import Data.Monoid
import qualified Data.List as List

type Name = String
type Args = [(Name, TypeAnnotation)]
type Label = Maybe Name

type Bits = [Bool]

type TypeAnnotation = Maybe SAWType

data Pattern
  = Literal Bits deriving Show
--  | Wildcard     
--  | Concat        deriving Eq

data ArrowType
  = Let
  | Fun
  | Inj
  | Sur
  | Iso deriving (Eq, Show)

data Expr a
  = Var Name                          a
  | Pattern Pattern                   a
  | Func ArrowType Args (Expr a)      a
  | App (Expr a) (Expr a)             a
  | Switch (Expr a) [(Expr a,Expr a)] a
  | DM [(Maybe Name, Expr a)]         a deriving Show

data SAWType
  = TypeVariable String
  | Atom Name SAWType
  | BitField [Integer]
  | DirectedMultiset [SAWType]
  | Arrow SAWType SAWType      deriving Show

instance Foldable Expr where
  foldMap f (Var _ a) =
    f a

  foldMap f (Pattern _ a) =
    f a

  foldMap f (Func _ _ e a) =
    (foldMap f e) `mappend` (f a)

  foldMap f (App e1 e2 a) =
    (foldMap f e1) `mappend` (foldMap f e2) `mappend` (f a)

  foldMap f (Switch e es a) =
    (foldMap f e) `mappend` (List.foldl foldCase mempty es) `mappend` (f a)
    where
      foldCase acc (guard, expr) = acc `mappend` (foldMap f guard) `mappend` (foldMap f expr)

  foldMap f (DM es a) =
    (List.foldl foldElem mempty es) `mappend` (f a)
    where
      foldElem acc (_,expr) = acc `mappend` (foldMap f expr)

instance Functor Expr where
  fmap f (Var n a) =
    Var n (f a)

  fmap f (Pattern p a) =
    Pattern p (f a)

  fmap f (Func t as e a) =
    Func t as (fmap f e) (f a)

  fmap f (App e1 e2 a) =
    App (fmap f e1) (fmap f e2) (f a)

  fmap f (Switch e es a) =
    Switch (fmap f e) (map mapCase es) (f a)
    where
      mapCase (guard, expr) = (fmap f guard, fmap f expr)

  fmap f (DM es a) =
    DM (map mapElem es) (f a)
    where
      mapElem (b,expr) = (b, fmap f expr)

instance Traversable Expr where
  traverse f (Var n a) = 
    Var n <$> f a

  traverse f (Pattern p a) = 
    Pattern p <$> f a

  traverse f (Func t args e a) =
    (Func t args) <$> traverse f e <*> f a

  traverse f (App e1 e2 a) =
    App <$> traverse f e1 <*> traverse f e2 <*> f a

  traverse f (Switch e es a) =
    Switch <$> traverse f e <*> (sequenceA (List.map mapCase es)) <*> f a
    where
      mapCase (guard,expr) =
        (,) <$> traverse f guard <*> traverse f expr

  traverse f (DM es a) =
    DM <$> (sequenceA (List.map mapElem es)) <*> f a
    where
      mapElem (b,expr) = 
        (,) b <$> traverse f expr

-- TODO quickcheck fmap should be equivalent to traversal with the 
--   identity applicative functor (fmapDefault).
-- TODO quickcheck foldMap should be equivalent to traversal with a
--   constant applicative functor (foldMapDefault).