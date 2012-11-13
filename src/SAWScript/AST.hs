{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.AST where

import Data.List
import Text.PrettyPrint.HughesPJ
import Control.Applicative

data Module a = Module
  { declarations :: [TopStmt a]
  , main         :: [BlockStmt a]
  }
  deriving (Eq,Show)

data TopStmt a
  = Import      Name               (Maybe [Name])   (Maybe Name)
  | TypeDef     Name               a
  | TopTypeDecl Name               a
  | TopLet      [(Name,Expr a)]
  deriving (Eq,Show)

data BlockStmt a
  = Bind          (Maybe Name)     (Expr a)
  | BlockTypeDecl Name             a
  | BlockLet      [(Name,Expr a)]
  deriving (Eq,Show)

data Expr a
  -- Constants
  = Bit         Bool                          a
  | Quote       String                        a
  | Z           Integer                       a
  -- Structures
  | Array       [Expr a]                      a
  | Block       [BlockStmt a]                 a
  | Tuple       [Expr a]                      a
  | Record      [(Name, Expr a)]              a
  -- Accessors
  | Index       (Expr a)           (Expr a)   a
  | Lookup      (Expr a)           Name       a
  -- LC
  | Var         Name                          a
  | Function    Name a             (Expr a)   a
  | Application (Expr a)           (Expr a)   a
  -- Sugar
  | LetBlock    [(Name,Expr a)]    (Expr a)
  deriving (Eq,Show)

data TypeF f
  -- Constants
  = Bit'
  | Z'
  | Quote'
  -- Structures
  | Array'       (Mu TypeF f)          Int
  | Block'       Context               (Mu TypeF f)
  | Tuple'       [Mu TypeF f]
  | Record'      [(Name,Mu TypeF f)]
  -- LC
  | Function'    (Mu TypeF f)          (Mu TypeF f)
  | Syn          String

instance Show (Mu TypeF Poly) where
  show pt = case pt of
    NoAnn   -> "NoAnn"
    Annot t -> "(Annot " ++ show t ++ ")"
    Poly n  -> "(Poly " ++ show n ++ ")"

instance Show (Mu TypeF Logic) where
  show lt = case lt of
    LVar i -> "(LVar " ++ show i ++ ")"
    Term t -> "(Term " ++ show t ++ ")"

instance Show (Mu TypeF Id) where
  show (Id t) = show t

instance Show (Mu TypeF a) => Show (TypeF a) where
  show t = case t of
    Bit'          -> "Bit'"
    Z'            -> "Z'"
    Quote'        -> "Quote'"
    Syn n         -> "(Syn " ++ n ++ ")"
    Array' t l    -> "(Array' " ++ show t ++ " " ++ show l ++ ")"
    Block' c t    -> "(Block' " ++ show c ++ " " ++ show t ++ ")"
    Tuple' ts     -> "(Tuple' " ++ show ts ++ ")"
    Record' fts   -> "(Record' " ++ show fts ++ ")"
    Function' a t -> "(Function' " ++ show a ++ " " ++ show t ++ ")"

instance Eq (Mu TypeF Poly) where
 NoAnn      == NoAnn      = True
 (Annot t1) == (Annot t2) = t1 == t2
 (Poly n1)  == (Poly n2)  = n1 == n2
 _          == _          = False

instance Eq (Mu TypeF Logic) where
  (LVar i1) == (LVar i2) = i1 == i2
  (Term t1) == (Term t2) = t1 == t2
  _         == _         = False

instance Eq (Mu TypeF Id) where
  (Id t1) == (Id t2) = t1 == t2

instance Eq (Mu TypeF a) => Eq (TypeF a) where
  Syn n1          == Syn n2          = n1 == n2
  Bit'            == Bit'            = True
  Z'              == Z'              = True
  Quote'          == Quote'          = True
  Array' t1 l1    == Array' t2 l2    = True
  Block' c1 t1    == Block' c2 t2    = c1 == c2 && t1 == t2
  Tuple' ts1      == Tuple' ts2      = ts1 == ts2
  Record' fts1    == Record' fts2    = fts1 == fts2
  Function' a1 t1 == Function' a2 t2 = a1 == a2 && t1 == t2
  _               == _               = False

class FixFunctor (a :: (* -> *) -> *) where
  fixmapM :: Monad m => (Mu a t -> m (Mu a f)) -> a t -> m (a f)

instance FixFunctor TypeF where
  fixmapM f t = case t of
    Syn n         -> return $ Syn n
    Bit'          -> return Bit'
    Z'            -> return Z'
    Quote'        -> return Quote'
    Array' t l    -> do t' <- f t
                        return (Array' t' l)
    Block' c t    -> do t' <- f t
                        return (Block' c t')
    Tuple' ts     -> do ts' <- mapM f ts
                        return (Tuple' ts')
    Record' fts   -> let (ns,ts) = unzip fts in
                       do ts' <- mapM f ts
                          return (Record' $ zip ns ts')
    Function' a t -> do a' <- f a
                        t' <- f t
                        return (Function' a' t')

data Context = Context deriving (Eq,Show)

type Name = String

data Poly a
  = NoAnn
  | Annot a
  | Poly Name

instance Functor Poly where
  fmap f p = case p of
    NoAnn   -> NoAnn
    Annot a -> Annot $ f a
    Poly n  -> Poly n

data Logic a
  = LVar Int
  | Term a

instance Functor Logic where
  fmap f l = case l of
    LVar i -> LVar i
    Term a -> Term $ f a

newtype Id a = Id a

instance Functor Id where
  fmap f (Id a) = Id $ f a

type Mu t f = f (t f)
type PType = Mu TypeF Poly
type LType = Mu TypeF Logic
type Type  = Mu TypeF Id

typeOf :: Expr a -> a
typeOf e = case e of
  Bit _ t           -> t
  Quote _ t         -> t
  Z _ t             -> t
  Array _ t         -> t
  Block _ t         -> t
  Tuple _ t         -> t
  Record _ t        -> t
  Index _ _ t       -> t
  Lookup _ _ t      -> t
  Var _ t           -> t
  Function _ _ _ t  -> t
  Application _ _ t -> t
  LetBlock _ e      -> typeOf e

