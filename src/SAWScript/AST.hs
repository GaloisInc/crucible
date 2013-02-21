{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWScript.AST where

import SAWScript.Unify

import Control.Monad
import Data.List

import Data.Foldable hiding (concat, elem)
import Data.Traversable

type MPType = Maybe (Mu (I :+: TypeF :+: Poly))
type PType = Mu (I :+: TypeF :+: Poly)
type LType = Mu (I :+: TypeF :+: Logic)
type CType = Mu (I :+: TypeF)

-- Expr Level {{{

type Module a = Module' a a

data Module' a b = Module
  { declarations :: [TopStmt a]
  , mainBlock    :: [BlockStmt b]
  }
  deriving (Functor,Foldable,Traversable)

data TopStmt a
  = Import      Name               (Maybe [Name])   (Maybe Name)
  | TypeDef     Name               PType
  | TopTypeDecl Name               PType
  | TopBind     Name               (Expr a)
  deriving (Functor,Foldable,Traversable)

data BlockStmt a
  = Bind          (Maybe Name)     Context (Expr a)
  | BlockTypeDecl Name             PType
  | BlockLet      [(Name,Expr a)]
  deriving (Functor,Foldable,Traversable)

data Expr a
  -- Constants
  = Unit                                      a
  | Bit         Bool                          a
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
  deriving (Functor,Foldable,Traversable)

instance (Show a,Show b) => Show (Module' a b) where
  show (Module ds mb) = (intercalate "\n" $ map show ds) ++ "\n\n" ++ (intercalate "\n" $ map show mb)

instance Show a => Show (TopStmt a) where
  show s = case s of
    Import n ns qn   -> case qn of
      Nothing -> "import " ++ n ++ maybe "" (\ns -> " (" ++ intercalate ", " ns ++ ")") ns
      Just q  -> "import qualified " ++ n ++ maybe "" (\ns -> " (" ++ intercalate ", " ns ++ ")") ns ++ " as " ++ q
    TypeDef n pt     -> "type " ++ n ++ " = " ++ show pt
    TopTypeDecl n pt -> n ++ " :: " ++ show pt
    TopBind n e      -> n ++ " = " ++ show e

instance Show a => Show (BlockStmt a) where
  show s = case s of
    Bind mn c e        -> case mn of
      Nothing -> show e
      Just n  -> n ++ " <- " ++ show e
    BlockTypeDecl n pt -> "let " ++ n ++ " :: " ++ show pt
    BlockLet nes       -> "let " ++ (intercalate "; " $ map (\(n,e) -> n ++ " = " ++ show e) nes)

instance Show a => Show (Expr a) where
  show e = case e of
    Unit mt             -> showMaybe mt $ "()"
    Bit b mt            -> showMaybe mt $ if b then "'1" else "'0"
    Quote s mt          -> showMaybe mt $ show s
    Z i mt              -> showMaybe mt $ show i
    Array es mt         -> showMaybe mt $ "[" ++ (intercalate ", " $ map show es) ++ "]"
    Block ss mt         -> showMaybe mt $ intercalate "\n" $ ("do" : map (("  " ++) . show) ss)
    Tuple es mt         -> showMaybe mt $ "(" ++ (intercalate ", " $ map show es) ++ ")"
    Record nes mt       -> showMaybe mt $ "{" ++ (intercalate ", " $ map (\(n,e) -> n ++ " = " ++ show e) nes) ++ "}"
    Index ar ix mt      -> showMaybe mt $ "(" ++ show ar ++ " ! " ++ show ix ++ ")"
    Lookup r f mt       -> showMaybe mt $ "(" ++ show r ++ "." ++ show f ++ ")"
    Var n mt            -> showMaybe mt $ n
    Function an at b mt -> showMaybe mt $ "(\\" ++ an ++ " :: " ++ show at ++ " -> " ++ show b ++ ")"
    Application f v mt  -> showMaybe mt $ "(" ++ show f ++ " " ++ show v ++ ")"
    LetBlock nes b      -> "(let " ++ (intercalate "; " $ map (\(n,e) -> n ++ " = " ++ show e) nes) ++ " in " ++ show b ++ ")"

showMaybe :: Show a => a -> String -> String
showMaybe t s = "(" ++ s ++ " :: " ++ show t ++ ")"

type Name = String
data Context
  = CryptolSetupContext
  | JavaSetupContext
  | LLVMSetupContext
  | VerifyScriptContext
  | TopLevelContext
  deriving (Eq,Show)

-- }}}

-- TypeF {{{

data TypeF a
  -- Constants
  = Unit'
  | Bit'
  | Z'
  | Quote'
  -- Structures
  | Array'       a          a
  | Block'       Context    a
  | Tuple'       [a]
  | Record'      [(Name,a)]
  -- LC
  | Function'    a          a
  | Syn          Name
  deriving (Show,Functor,Foldable,Traversable)

data Type 
  = UnitT
  | BitT
  | ZT
  | QuoteT
  | ArrayT Type Int
  | BlockT Context Type
  | TupleT [Type]
  | RecordT [(Name,Type)]
  | FunctionT Type Type
  deriving (Eq,Show)

-- }}}

-- Equal Instances {{{

instance Equal TypeF where
  equal t1 t2 = case (t1,t2) of
    (Unit',Unit')                             -> True
    (Bit',Bit')                               -> True
    (Z',Z')                                   -> True
    (Quote',Quote')                           -> True
    (Array' t1' l1,Array' t2' l2)             -> l1 == l2 && t1' == t2'
    (Block' c1 t1',Block' c2 t2')             -> c1 == c2 && t1' == t2'
    (Tuple' ts1',Tuple' ts2')                 -> ts1' == ts2'
    (Record' fts1',Record' fts2')             -> fts1' == fts2'
    (Function' at1' bt1',Function' at2' bt2') -> at1' == at2' && bt1' == bt2'
    (Syn n1,Syn n2)                           -> n1 == n2
    _                                         -> False
-- }}}

-- Render {{{
instance Render TypeF where
  render t = case t of
    Unit'           -> "Unit"
    Bit'            -> "Bit"
    Z'              -> "Z"
    Quote'          -> "Quote"
    Array' t l      -> "[" ++ show l ++ "]" ++ show t
    Block' c t      -> "(Block " ++ show c ++ " " ++ show t ++ ")"
    Tuple' ts       -> "(" ++ (intercalate ", " $ map show ts) ++ ")"
    Record' fts     -> "{" ++ (intercalate ", " $ map (\(n,t)-> n ++ " :: " ++ show t) fts) ++ "}"
    Function' at bt -> "(" ++ show at ++ " -> " ++ show bt ++ ")"
    Syn n           -> n
-- }}}

-- Uni {{{
instance Uni TypeF where
  uni t1 t2 = case (t1,t2) of
    (Array' t1' l1,Array' t2' l2)             -> unify l1 l2 >> unify t1' t2'
    (Block' c1 t1',Block' c2 t2')             -> assert (c1 == c2) ("Could not match contexts " ++ show c1 ++ " and " ++ show c2) >> unify t1' t2'
    (Tuple' ts1',Tuple' ts2')                 -> zipWithMP_ unify ts1' ts2'
    (Record' fts1',Record' fts2')             -> do conj [ disj [ unify x y | (nx,x) <- fts1', nx == ny ] | (ny,y) <- fts2' ]
                                                    conj [ disj [ unify y x | (ny,y) <- fts2', nx == ny ] | (nx,x) <- fts1' ]
    (Function' at1' bt1',Function' at2' bt2') -> unify at1' at2' >> unify bt1' bt2'
    _                                         -> fail ("TypeF Mismatch: " ++ render t1 ++ " could not be unified with " ++ render t2)
-- }}}

-- Operators {{{

unit :: (TypeF :<: f) => Mu f
unit = inject Unit'

bit :: (TypeF :<: f) => Mu f
bit = inject Bit'

quote :: (TypeF :<: f) => Mu f
quote = inject Quote'

z :: (TypeF :<: f) => Mu f
z = inject Z'

array :: (I :<: f, TypeF :<: f) => Mu f -> Mu f -> Mu f
array t l = inject $ Array' t l

block :: (TypeF :<: f) => Context -> Mu f -> Mu f
block c t = inject $ Block' c t

tuple :: (TypeF :<: f) => [Mu f] -> Mu f
tuple ts = inject $ Tuple' ts

record :: (TypeF :<: f) => [(Name,Mu f)] -> Mu f
record fts = inject $ Record' fts

function :: (TypeF :<: f) => Mu f -> Mu f -> Mu f
function at bt = inject $ Function' at bt

syn :: (TypeF :<: f) => String -> Mu f
syn n = inject $ Syn n

-- }}}

-- I {{{

data I a = I Int deriving (Show,Functor,Foldable,Traversable)

instance Equal I where
  equal (I x) (I y) = x == y

instance Render I where
  render (I x) = show x

instance Uni I where
  uni (I x) (I y) = fail ("I: " ++ show x ++ " =/= " ++ show y)

i :: (I :<: f) => Int -> Mu f
i x = inject $ I x

-- }}}

-- Poly {{{

data Poly a = Poly Name deriving (Show,Functor,Foldable,Traversable)

instance Render Poly where render (Poly n) = n

instance Equal Poly where
  equal (Poly n1) (Poly n2) = n1 == n2

instance Uni Poly where
  uni (Poly n1) (Poly n2) = fail ("Poly: " ++ show n1 ++ " =/= " ++ show n2)

poly :: (Poly :<: f) => String -> Mu f
poly n = inject $ Poly n

-- }}}

class Functor f => Decorated f where
  decor :: f a -> a

instance Decorated Expr where
  decor e = case e of
    Unit t            -> t
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
    LetBlock _ e      -> decor e

context :: BlockStmt a -> Maybe Context
context s = case s of
  Bind _ c _ -> Just c
  _          -> Nothing

-- Tests {{{

m1 :: Module MPType
m1 = Module
  { declarations =
    [ Import "Foo" Nothing Nothing
    , TypeDef "Test" bit
    , TopTypeDecl "map4" (function (function (poly "a") (poly "b")) (function (array (poly "a") (poly "m")) (array (poly "b") (poly "m"))))
    , TopTypeDecl "a1" (array z (i 4))
    , TopTypeDecl "plus1" (function z z)
    ]
  , mainBlock = 
    [ Bind Nothing TopLevelContext (Application (Var "map4" Nothing) (Var "plus1" Nothing) (Just $ function (array (poly "a") (i 3)) (array (poly "b") (i 3))))
    --[ Bind Nothing TopLevelContext (Var "map4" Nothing)
    ]
  }

m1b :: Module MPType
m1b = Module
  { declarations =
    [ Import "Foo" Nothing Nothing
    , TypeDef "Test" bit
    , TopTypeDecl "map4" (function (function (poly "a") (poly "b")) (function (array (poly "a") (poly "m")) (array (poly "b") (poly "m"))))
    , TopTypeDecl "a1" (array z (i 4))
    , TopTypeDecl "plus1" (function (syn "Test") (syn "Test"))
    ]
  , mainBlock = 
    [ Bind Nothing TopLevelContext (Application (Var "map4" Nothing) (Var "plus1" Nothing) Nothing)
    ]
  }

m1c :: Module MPType
m1c = Module
  { declarations =
    [ Import "Foo" Nothing Nothing
    , TypeDef "Test" bit
    , TopTypeDecl "map4" (function (function (poly "a") (poly "b")) (function (array (poly "a") (poly "m")) (array (poly "b") (poly "m"))))
    , TopTypeDecl "a1" (array (syn "Test") (i 5))
    , TopTypeDecl "plus1" (function (syn "Test") (syn "Test"))
    ]
  , mainBlock = 
    [ Bind Nothing TopLevelContext (Application (Application (Var "map4" Nothing) (Var "plus1" Nothing) Nothing) (Var "a1" Nothing) Nothing)
    ]
  }

m2 :: Module MPType
m2 = Module
  { declarations =
    [ Import "Foo" Nothing Nothing
    , TypeDef "Test" bit
    , TopTypeDecl "map4" (function (function (poly "a") (poly "b")) (function (array (poly "a") (poly "m")) (array (poly "b") (poly "m"))))
    , TopTypeDecl "a1" (array z (poly "n"))
    , TopTypeDecl "plus1" (function z z)
    ]
  , mainBlock = 
    [ Bind Nothing TopLevelContext (Var "map4" (Just (function (poly "a") (poly "a"))))
    ]
  }

m2b :: Module MPType
m2b = Module
  { declarations =
    [ TopTypeDecl "map4" (function (function (poly "a") (poly "b")) (function (array (poly "a") (poly "m")) (array (poly "b") (poly "m"))))
    ]
  , mainBlock = 
    [ Bind Nothing TopLevelContext (Var "map4" (Just (function (poly "a") (poly "b"))))
    ]
  }

m3 :: Module MPType
m3 = Module
  { declarations = []
  , mainBlock = [ Bind Nothing TopLevelContext (Bit True Nothing) ]
  }

m4 :: Module MPType
m4 = Module
  { declarations = [ TopTypeDecl "a" bit ]
  , mainBlock =
    [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

m5 :: Module MPType
m5 = Module
  { declarations =
    [ TopBind "a" (Bit True Nothing) ]
  , mainBlock =
    [ Bind Nothing TopLevelContext (Var "a" Nothing) 
    ]
  }

m6 :: Module MPType
m6 = Module
  { declarations =
    [ TopTypeDecl "map4" (function (function (poly "a") (poly "b")) (function (array (poly "a") (poly "m")) (array (poly "b") (poly "m")))) ]
  , mainBlock = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferBit :: Module MPType
inferBit = Module
  { declarations = [ TopBind "a" (Bit True Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferQuote :: Module MPType
inferQuote = Module
  { declarations = [ TopBind "a" (Quote "foo" Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferZ :: Module MPType
inferZ = Module
  { declarations = [ TopBind "a" (Z 31337 Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferBlock :: Module MPType
inferBlock = Module
  { declarations = [ TopBind "a" (Block [ Bind Nothing TopLevelContext (Bit True Nothing) ] Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferTuple :: Module MPType
inferTuple = Module
  { declarations = [ TopBind "a" (Tuple [Bit True Nothing, Quote "foo" Nothing, Z 31337 Nothing] Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferRecord1 :: Module MPType
inferRecord1 = Module
  { declarations = [ TopBind "a" (Record [("foo",Quote "foo" Nothing)] Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferRecord2 :: Module MPType
inferRecord2 = Module
  { declarations = [ TopBind "a" (Record [("foo",Quote "foo" Nothing),("bar",Z 42 Nothing)] Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferArray1 :: Module MPType
inferArray1 = Module
  { declarations = [ TopBind "a" (Array [Quote "foo" Nothing, Quote "bar" Nothing] Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

inferArray2 :: Module MPType
inferArray2 = Module
  { declarations = [ TopBind "a" (Array [Quote "foo" Nothing, Z 42 Nothing] Nothing) ]
  , mainBlock    = [ Bind Nothing TopLevelContext (Var "a" Nothing) ]
  }

-- }}}

updateAnnotation :: Expr a -> a -> Expr a
updateAnnotation e t = case e of
  Unit _            -> Unit t
  Bit x _           -> Bit x t
  Quote x _         -> Quote x t
  Z x _             -> Z x t
  Array x _         -> Array x t
  Block x _         -> Block x t
  Tuple x _         -> Tuple x t
  Record x _        -> Record x t
  Index x y _       -> Index x y t
  Lookup x y _      -> Lookup x y t
  Var x _           -> Var x t
  Function x y z _  -> Function x y z t
  Application x y _ -> Application x y t
  LetBlock x e      -> LetBlock x (updateAnnotation e t)

synToPoly :: [Name] -> PType -> PType
synToPoly ns ty = case prj (out ty) of
  Just (Array' ty1 ty2)      -> array (synToPoly ns ty1) (synToPoly ns ty2)
  Just (Block' ctx ty1)      -> block ctx (synToPoly ns ty1)
  Just (Tuple' tys)          -> tuple $ map (synToPoly ns) tys
  Just (Record' flds)        -> record $ map (\(n, t) -> (n, synToPoly ns t)) flds
  Just (Function' ty1 ty2)   -> function (synToPoly ns ty1) (synToPoly ns ty2)
  Just (Syn n) | n `elem` ns -> poly n
  _ -> ty
