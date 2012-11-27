{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.AST where

import SAWScript.FixFunctor

import Data.List
import Control.Applicative
import Control.Monad

-- Expr Level {{{

data Module a = Module
  { declarations :: [TopStmt a]
  , main         :: [BlockStmt a]
  }
  deriving Show

data TopStmt a
  = Import      Name               (Maybe [Name])   (Maybe Name)
  | TypeDef     Name               CType
  | TopTypeDecl Name               CType
  | TopLet      [(Name,Expr a)]
  deriving Show

data BlockStmt a
  = Bind          (Maybe Name)     (Expr a)
  | BlockTypeDecl Name             CType
  | BlockLet      [(Name,Expr a)]
  deriving Show

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
  | Function    Name     a         (Expr a)   a
  | Application (Expr a)           (Expr a)   a
  -- Sugar
  | LetBlock    [(Name,Expr a)]    (Expr a)
  deriving Show

type Name = String
data Context = Context deriving (Eq,Show)

-- }}}

-- Type Level {{{

data Type a
  -- Constants
  = Bit'
  | Z'
  | Quote'
  -- Structures
  | Array'       a          Int
  | Block'       Context    a
  | Tuple'       [a]
  | Record'      [(Name,a)]
  -- LC
  | Function'    a          a
  | Syn          String

data Poly a = Poly Name
instance Functor Poly where fmap f (Poly n) = Poly n

data Logic a = LVar Int
instance Functor Logic where fmap f (LVar i) = LVar i

type MPType = Maybe (Mu (Type :+: Poly))
type PType = Mu (Type :+: Poly)
type LType = Mu (Type :+: Logic)
type CType = Mu Type

instance Render Type where
  render t = case t of
    Bit'            -> "Bit"
    Z'              -> "Z"
    Quote'          -> "Quote"
    Array' t l      -> "[" ++ show l ++ "]" ++ show t
    Block' c t      -> show c ++ " " ++ show t
    Tuple' ts       -> "(" ++ (intercalate ", " $ map show ts) ++ ")"
    Record' fts     -> "{" ++ (intercalate ", " $ map (\(n,t)-> n ++ " :: " ++ show t) fts) ++ "}"
    Function' at bt -> "(" ++ show at ++ " -> " ++ show bt ++ ")"
    Syn n           -> n

instance Render Poly where render (Poly n) = n

instance Render Logic where render (LVar i) = "_." ++ show i

-- }}}

-- Functor instances {{{

instance Functor Module where
  fmap f m = m { declarations = map (fmap f) $ declarations m
               , main         = map (fmap f) $ main m
               }

instance Functor TopStmt where
  fmap f s = case s of
    Import n mns mn -> Import n mns mn
    TypeDef n t     -> TypeDef n t
    TopTypeDecl n t -> TopTypeDecl n t
    TopLet binds    -> let (ns,es) = unzip binds in
                         TopLet $ zip ns $ map (fmap f) es

instance Functor BlockStmt where
  fmap f s = case s of
    Bind n e          -> Bind n $ fmap f e
    BlockTypeDecl n t -> BlockTypeDecl n t
    BlockLet binds    -> let (ns,es) = unzip binds in
                           BlockLet $ zip ns $ map (fmap f) es

instance Functor Expr where
  fmap f e = case e of
    Bit b a                   -> Bit b $ f a
    Quote s a                 -> Quote s $ f a
    Z i a                     -> Z i $ f a
    Array es a                -> Array (map (fmap f) es) $ f a
    Block ss a                -> Block (map (fmap f) ss) $ f a
    Tuple es a                -> Tuple (map (fmap f) es) $ f a
    Record nes a              -> let (ns,es) = unzip nes in
                                   Record (zip ns $ map (fmap f) es) $ f a
    Index ar ix a             -> Index (fmap f ar) (fmap f ix) $ f a
    Lookup rc fl a            -> Lookup (fmap f rc) fl $ f a
    Var n a                   -> Var n $ f a
    Function argn argt body a -> Function argn (f argt) (fmap f body) $ f a
    Application fn v a        -> Application (fmap f fn) (fmap f v) $ f a
    LetBlock binds body       -> let (ns,es) = unzip binds in
                                   LetBlock (zip ns $ map (fmap f) es) (fmap f body)

instance Functor Type where
  fmap f t = case t of
    Bit'              -> Bit'
    Z'                -> Z'
    Quote'            -> Quote'
    Array' t' l       -> Array' (f t') l
    Block' c t'       -> Block' c (f t')
    Tuple' ts'        -> Tuple' (map f ts')
    Record' fts'      -> let (ns,ts') = unzip fts' in
                           Record' (zip ns $ map f ts')
    Function' at' bt' -> Function' (f at') (f bt')
    Syn n             -> Syn n

-- }}}

-- Equal Instances {{{

instance Equal Type where
  equal t1 t2 = case (t1,t2) of
    (Bit',Bit')                               -> True
    (Z',Z')                                   -> True
    (Quote',Quote')                           -> True
    (Array' t1' l1,Array' t2' l2)             -> t1' == t2' && l1 == l2
    (Block' c1 t1',Block' c2 t2')             -> c1 == c2 && t1' == t2'
    (Tuple' ts1',Tuple' ts2')                 -> ts1' == ts2'
    (Record' fts1',Record' fts2')             -> fts1' == fts2'
    (Function' at1' bt1',Function' at2' bt2') -> at1' == at2' && bt1' == bt2'
    (Syn n1,Syn n2)                           -> n1 == n2
    _                                         -> False

instance Equal Logic where
  equal (LVar x) (LVar y) = x == y

-- }}}

-- Operators {{{1

poly :: (Poly :<: f) => String -> Mu f
poly n = inject $ Poly n

lVar :: (Logic :<: f) => Int -> Mu f
lVar i = inject $ LVar i

bit :: (Type :<: f) => Mu f
bit = inject Bit'

quote :: (Type :<: f) => Mu f
quote = inject Quote'

z :: (Type :<: f) => Mu f
z = inject Z'

array :: (Type :<: f) => Mu f -> Int -> Mu f
array t l = inject $ Array' t l

block :: (Type :<: f) => Context -> Mu f -> Mu f
block c t = inject $ Block' c t

tuple :: (Type :<: f) => [Mu f] -> Mu f
tuple ts = inject $ Tuple' ts

record :: (Type :<: f) => [(Name,Mu f)] -> Mu f
record fts = inject $ Record' fts

function :: (Type :<: f) => Mu f -> Mu f -> Mu f
function at bt = inject $ Function' at bt

syn :: (Type :<: f) => String -> Mu f
syn n = inject $ Syn n

-- }}}

annotation :: Expr a -> a
annotation e = case e of
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
  LetBlock _ e      -> annotation e

