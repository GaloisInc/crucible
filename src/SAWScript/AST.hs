{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.AST
       ( Name
       , LName
       , Bind
       , Located(..)
       , Import(..)
       , Expr(..)
       , Stmt(..)
       , DeclGroup(..)
       , Decl(..)
       , Context(..)
       , Type(..), TypeIndex
       , TyCon(..)
       , Schema(..)
       , toLName
       , tMono, tForall, tTuple, tRecord, tArray, tFun
       , tString, tTerm, tType, tBool, tZ, tAIG
       , tBlock, tContext, tVar

       , PrettyPrint(..), pShow, commaSepAll
       ) where

import SAWScript.Token
import SAWScript.Utils

import Data.Map (Map)
import qualified Data.Map as Map

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
#endif
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Cryptol.Parser.AST as P (ImportSpec, ModName)

-- Names {{{

type Name = String

type Bind a = (Name,a)

-- }}}

-- Expr Level {{{

data Located a = Located { getVal :: a, getOrig :: Name, getPos :: Pos } deriving (Functor, Foldable, Traversable)
instance Show (Located a) where
  show (Located _ v p) = show v ++ " (" ++ show p ++ ")"

type LName = Located Name

instance Eq a => Eq (Located a) where
  a == b = getVal a == getVal b

instance Ord a => Ord (Located a) where
  compare a b = compare (getVal a) (getVal b)

toLName :: Token Pos -> LName
toLName p = Located (tokStr p) (tokStr p) (tokPos p)

data Import = Import
  { iModule    :: Either FilePath P.ModName
  , iAs        :: Maybe P.ModName
  , iSpec      :: Maybe P.ImportSpec
  } deriving (Eq, Show)

data Expr
  -- Constants
  = Bit Bool
  | String String
  | Z Integer
  | Code (Located String)
  | CType (Located String)
  -- Structures
  | Array  [Expr]
  | Block  [Stmt]
  | Tuple  [Expr]
  | Record (Map Name Expr)
  -- Accessors
  | Index  Expr Expr
  | Lookup Expr Name
  | TLookup Expr Integer
  -- LC
  | Var (Located Name)
  | Function    LName (Maybe Type) Expr
  | Application Expr Expr
  -- Sugar
  | Let DeclGroup Expr
  | TSig Expr Type
  deriving (Eq, Show)

data Stmt
  = StmtBind     (Maybe LName) (Maybe Type) (Maybe Type) Expr
  | StmtLet      DeclGroup
  | StmtCode     (Located String)
  | StmtImport   Import
  deriving (Eq, Show)

data DeclGroup
  = Recursive [Decl]
  | NonRecursive Decl
  deriving (Eq, Show)

data Decl
  = Decl { dName :: LName, dType :: Maybe Schema, dDef :: Expr }
  deriving (Eq, Show)

-- }}}

-- Type Level {{{

data Context
  = CryptolSetup
  | JavaSetup
  | LLVMSetup
  | ProofScript
  | TopLevel
  deriving (Eq,Show)

data Type
  = TyCon TyCon [Type]
  | TyRecord (Map Name Type)
  | TyVar Name
  | TyUnifyVar TypeIndex       -- ^ For internal typechecker use only
  | TySkolemVar Name TypeIndex -- ^ For internal typechecker use only
  deriving (Eq,Show)

type TypeIndex = Integer

data TyCon
  = TupleCon Integer
  | ArrayCon
  | FunCon
  | StringCon
  | TermCon
  | TypeCon
  | BoolCon
  | ZCon
  | BlockCon
  | AIGCon
  | ContextCon Context
  deriving (Eq, Show)

data Schema = Forall [Name] Type
  deriving (Eq, Show)

-- }}}

-- Pretty Printing {{{

pShow :: PrettyPrint a => a -> String
pShow = show . pretty 0

class PrettyPrint p where
  pretty :: Int -> p -> PP.Doc

instance PrettyPrint Schema where
  pretty _ (Forall ns t) = case ns of
    [] -> pretty 0 t
    _  -> PP.braces (commaSepAll $ map PP.text ns) PP.<+> pretty 0 t

instance PrettyPrint Type where
  pretty par t@(TyCon tc ts) = case (tc,ts) of
    (_,[])                 -> pretty par tc
    (TupleCon _,_)         -> PP.parens $ commaSepAll $ map (pretty 0) ts
    (ArrayCon,[typ])       -> PP.brackets (pretty 0 typ)
    (FunCon,[f,v])         -> (if par > 0 then PP.parens else id) $
                                pretty 1 f PP.<+> PP.text "->" PP.<+> pretty 0 v
    (BlockCon,[cxt,typ])   -> (if par > 1 then PP.parens else id) $
                                pretty 1 cxt PP.<+> pretty 2 typ
    _ -> error $ "malformed TyCon: " ++ show t
  pretty _par (TyRecord fs) =
      PP.braces
    $ commaSepAll
    $ map (\(n,t) -> PP.text n `prettyTypeSig` pretty 0 t)
    $ Map.toList fs
  pretty _par (TyUnifyVar i)    = PP.text "t." PP.<> PP.integer i
  pretty _par (TySkolemVar n i) = PP.text n PP.<> PP.integer i
  pretty _par (TyVar n)         = PP.text n

instance PrettyPrint TyCon where
  pretty par tc = case tc of
    TupleCon n     -> PP.parens $ replicateDoc (n - 1) $ PP.char ','
    ArrayCon       -> PP.parens $ PP.brackets $ PP.empty
    FunCon         -> PP.parens $ PP.text "->"
    StringCon      -> PP.text "String"
    TermCon        -> PP.text "Term"
    TypeCon        -> PP.text "Type"
    BoolCon        -> PP.text "Bit"
    ZCon           -> PP.text "Int"
    AIGCon         -> PP.text "AIG"
    BlockCon       -> PP.text "<Block>"
    ContextCon cxt -> pretty par cxt

instance PrettyPrint Context where
  pretty _ c = case c of
    CryptolSetup -> PP.text "CryptolSetup"
    JavaSetup    -> PP.text "JavaSetup"
    LLVMSetup    -> PP.text "LLVMSetup"
    ProofScript  -> PP.text "ProofScript"
    TopLevel     -> PP.text "TopLevel"

replicateDoc :: Integer -> PP.Doc -> PP.Doc
replicateDoc n d
  | n < 1 = PP.empty
  | True  = d PP.<> replicateDoc (n-1) d

prettyTypeSig :: PP.Doc -> PP.Doc -> PP.Doc
prettyTypeSig n t = n PP.<+> PP.char ':' PP.<+> t

commaSep :: PP.Doc -> PP.Doc -> PP.Doc
commaSep = ((PP.<+>) . (PP.<> PP.comma))

commaSepAll :: [PP.Doc] -> PP.Doc
commaSepAll ds = case ds of
  [] -> PP.empty
  _  -> foldl1 commaSep ds

-- }}}

-- Type Constructors {{{

tMono :: Type -> Schema
tMono = Forall []

tForall :: [Name] -> Schema -> Schema
tForall xs (Forall ys t) = Forall (xs ++ ys) t

tTuple :: [Type] -> Type
tTuple ts = TyCon (TupleCon $ fromIntegral $ length ts) ts

tRecord :: [(Name, Type)] -> Type
tRecord fields = TyRecord (Map.fromList fields)

tArray :: Type -> Type
tArray t = TyCon ArrayCon [t]

tFun :: Type -> Type -> Type
tFun f v = TyCon FunCon [f,v]

tString :: Type
tString = TyCon StringCon []

tTerm :: Type
tTerm = TyCon TermCon []

tType :: Type
tType = TyCon TypeCon []

tBool :: Type
tBool = TyCon BoolCon []

tAIG :: Type
tAIG = TyCon AIGCon []

tZ :: Type
tZ = TyCon ZCon []

tBlock :: Type -> Type -> Type
tBlock c t = TyCon BlockCon [c,t]

tContext :: Context -> Type
tContext c = TyCon (ContextCon c) []

tVar :: Name -> Type
tVar n = TyVar n

-- }}}
