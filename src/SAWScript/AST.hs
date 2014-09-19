{-# LANGUAGE DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.AST where

import SAWScript.Token
import SAWScript.Utils

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import System.FilePath (dropExtension)
import qualified Text.PrettyPrint.Leijen as PP

-- Intermediate Types {{{

type RawT      = Maybe Schema
type RawSigT   = Schema
type ResolvedT = Maybe Schema
type FullT     = Schema

-- }}}

-- Names {{{

type Name = String
-- dot separated names designating module heirarchy,
--  and single name designating module name.
newtype ModuleName = ModuleName Name deriving (Eq,Ord,Show)

-- some name, qualified with some dot separated names.
--  compiler doesn't know what those names are yet.
newtype UnresolvedName = UnresolvedName Name
  deriving (Eq,Ord,Show)

-- a name that has been resolved to a particular module.
data ResolvedName
  -- locally bound in the environment, ie. in a lambda.
  = LocalName Name
  -- a name bound at the top level of some module.
  | TopLevelName ModuleName Name
  deriving (Eq,Ord,Show)

moduleNameFromString :: String -> ModuleName
moduleNameFromString nm = ModuleName nm

moduleNameFromPath :: FilePath -> ModuleName
moduleNameFromPath fp = ModuleName (dropExtension fp)

renderDotSepName :: [Name] -> String
renderDotSepName = intercalate "."

renderModuleName :: ModuleName -> String
renderModuleName (ModuleName n) = n

moduleNameFilePath :: ModuleName -> String
moduleNameFilePath (ModuleName n) = n

renderUnresolvedName :: UnresolvedName -> String
renderUnresolvedName (UnresolvedName n) = n

renderResolvedName :: ResolvedName -> String
renderResolvedName rn = case rn of
  TopLevelName (ModuleName mn) n -> renderDotSepName $ [mn,n]
  LocalName n                    -> show n

type Bind a = (Name,a)
type LBind a = (LName, a)
onBind :: (a -> b) -> Bind a -> Bind b
onBind f (n,a) = (n,f a)
onBinds :: (a -> b) -> [Bind a] -> [Bind b]
onBinds = map . onBind

type Env a       = Map Name a
type LEnv a      = Map LName a
type ModuleEnv a = Map ModuleName a

singletonEnv :: Name -> a -> Env a
singletonEnv = Map.singleton

lookupEnv :: Name -> Env a -> Maybe a
lookupEnv = Map.lookup

lookupLEnv :: LName -> LEnv a -> Maybe a
lookupLEnv = Map.lookup

memberEnv :: Name -> Env a -> Bool
memberEnv = Map.member

unionEnv :: Env a -> Env a -> Env a
unionEnv = Map.union

emptyEnv :: Env a
emptyEnv = Map.empty

insertEnv :: Name -> a -> Env a -> Env a
insertEnv = Map.insert

unionsLEnv :: [LEnv a] -> LEnv a
unionsLEnv = Map.unions

-- }}}

-- Module Level {{{

data Module refT typeT = Module
  { moduleName         :: ModuleName
  , moduleExprEnv      :: [(LName, Expr refT typeT)]
  , modulePrimEnv      :: LEnv typeT
  , moduleDependencies :: ModuleEnv ValidModule
  , moduleCryDeps      :: [FilePath]
  } deriving (Eq,Show)

-- A fully type checked module.
--  Exprs have resolved names, concrete types
--  Types have ResolvedT (Nothing for abstract types, Just FullT for type synonyms)
type ValidModule = Module ResolvedName Schema

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

toNameDec :: (LName, a) -> (Name, a)
toNameDec = first getVal

type TopStmtSimple   = TopStmt   UnresolvedName
type ExprSimple      = Expr      UnresolvedName
type BlockStmtSimple = BlockStmt UnresolvedName

data TopStmt refT typeT
  = Import      ModuleName (Maybe [Name])    (Maybe Name)   -- ^ import <module> [(<names>)] [as <name>]
  | TopTypeDecl LName       Schema                          -- ^ <name> : <type>
  | TopBind     LName       (Expr refT typeT)               -- ^ <name> = <expr>
  | Prim        LName       RawT                            -- ^ prim <name> : <type>
  | ImportCry   FilePath                                    -- ^ import "filepath.cry"
  deriving (Eq,Show,Functor,Foldable,Traversable)

{-
data Exprs refT typeT
  = PrimExpr typeT
  | Defined (Expr refT typeT)
  deriving (Eq,Show,Functor,Foldable,Traversable)
-}

data Expr refT typeT
  -- Constants
  = Bit Bool     typeT
  | Quote String typeT
  | Z Integer    typeT
  | Undefined    typeT
  | Code (Located String) typeT
  -- Structures
  | Array  [Expr refT typeT]         typeT
  | Block  [BlockStmt refT typeT]    typeT
  | Tuple  [Expr refT typeT]         typeT
  | Record [Bind (Expr refT typeT)]  typeT
  -- Accessors
  | Index  (Expr refT typeT) (Expr refT typeT) typeT
  | Lookup (Expr refT typeT) Name              typeT
  | TLookup (Expr refT typeT) Integer          typeT
  -- LC
  | Var         (Located refT)  typeT
  | Function    LName  typeT       (Expr refT typeT) typeT
  | Application (Expr refT typeT) (Expr refT typeT) typeT
  -- Sugar
  | LetBlock [LBind (Expr refT typeT)] (Expr refT typeT)
  deriving (Eq,Show,Functor,Foldable,Traversable)

data BlockStmt refT typeT
 -- Bind          bind var         context   expr
  = Bind          (Maybe (LBind typeT))     typeT     (Expr refT typeT)
  | BlockLet      [(LName,Expr refT typeT)]
  | BlockCode     (Located String)
  deriving (Eq,Show,Functor,Foldable,Traversable)

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
  | TyVar TyVar
 deriving (Eq,Show)

data TyVar
  = FreeVar Integer
  | BoundVar Name
 deriving (Eq,Ord,Show)

data TyCon
 = TupleCon Integer
 | ArrayCon
 | FunCon
 | StringCon
 | TermCon
 | BoolCon
 | ZCon
 | BlockCon
 | ContextCon Context
 | AbstractCon String
 deriving (Eq,Show)

data Schema = Forall [Name] Type deriving (Eq, Show)

-- }}}

-- Pretty Printing {{{

pShow :: PrettyPrint a => a -> String
pShow = show . pretty True

class PrettyPrint p where
  -- Bool indicates whether term should be parenthesized, eg. if rendering is space separated.
  pretty :: Bool -> p -> PP.Doc

instance PrettyPrint Schema where
  pretty _ (Forall ns t) = case ns of
    [] -> pretty False t
    _  -> PP.braces (commaSepAll $ map PP.text ns) PP.<+> pretty False t

instance PrettyPrint Type where
  pretty par t@(TyCon tc ts) = case (tc,ts) of
    (_,[])                 -> pretty par tc
    (TupleCon _,_)         -> PP.parens $ commaSepAll $ map (pretty False) ts
    (ArrayCon,[len,TyCon BoolCon []]) -> PP.brackets (pretty False len)
    (ArrayCon,[len,typ])   -> PP.brackets (pretty False len) PP.<> (pretty True typ)
    (FunCon,[f,v])         -> (if par then PP.parens else id) $
                                pretty False f PP.<+> PP.text "->" PP.<+> pretty False v
    (BlockCon,[cxt,typ])   -> (if par then PP.parens else id) $
                                pretty True cxt PP.<+> pretty True typ
    _ -> error $ "malformed TyCon: " ++ pShow t
  pretty _par (TyRecord fs) =
      PP.braces
    $ commaSepAll
    $ map (\(n,t) -> PP.text n `prettyTypeSig` pretty False t)
    $ Map.toList fs
  pretty par (TyVar tv) = pretty par tv

instance PrettyPrint TyVar where
  pretty _par tv = case tv of
    FreeVar n  -> PP.text "fv." PP.<> PP.integer n
    BoundVar n -> PP.text n

instance PrettyPrint TyCon where
  pretty par tc = case tc of
    TupleCon n     -> PP.parens $ replicateDoc (n - 1) $ PP.char ','
    ArrayCon       -> PP.parens $ PP.brackets $ PP.empty
    FunCon         -> PP.parens $ PP.text "->"
    StringCon      -> PP.text "String"
    TermCon        -> PP.text "Term"
    BoolCon        -> PP.text "Bit"
    ZCon           -> PP.text "Int"
    BlockCon       -> PP.text "<Block>"
    ContextCon cxt -> pretty par cxt
    AbstractCon n  -> PP.text n

instance PrettyPrint Context where
  pretty _ c = case c of
    CryptolSetup -> PP.text "CryptolSetup"
    JavaSetup    -> PP.text "JavaSetup"
    LLVMSetup    -> PP.text "LLVMSetup"
    ProofScript  -> PP.text "ProofScript"
    TopLevel     -> PP.text "TopLevel"

instance PrettyPrint ModuleName where
  pretty _ mn = PP.text (renderModuleName mn)

instance PrettyPrint (Module refT typeT) where
  pretty par m = pretty par (moduleName m)

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

tBool :: Type
tBool = TyCon BoolCon []

tZ :: Type
tZ = TyCon ZCon []

tBlock :: Type -> Type -> Type
tBlock c t = TyCon BlockCon [c,t]

tContext :: Context -> Type
tContext c = TyCon (ContextCon c) []

tAbstract :: Name -> Type
tAbstract n = TyCon (AbstractCon n) []

boundVar :: Name -> Type
boundVar n = TyVar (BoundVar n)

-- }}}

-- Expr Accessors/Modifiers {{{

typeOf :: Expr refT typeT -> typeT
typeOf expr = case expr of
  Bit _ t           -> t
  Quote _ t         -> t
  Z _ t             -> t
  Undefined t       -> t
  Code _ t          -> t
  Array _ t         -> t
  Block _ t         -> t
  Tuple _ t         -> t
  Record _ t        -> t
  Index _ _ t       -> t
  Lookup _ _ t      -> t
  TLookup _ _ t     -> t
  Var _ t           -> t
  Function _ _ _ t  -> t
  Application _ _ t -> t
  LetBlock _ e'     -> typeOf e'

context :: BlockStmt refT typeT -> Maybe typeT
context s = case s of
  Bind _ c _ -> Just c
  _          -> Nothing

updateAnnotation :: typeT -> Expr refT typeT -> Expr refT typeT
updateAnnotation t expr = case expr of
  Bit x _           -> Bit x t
  Quote x _         -> Quote x t
  Z x _             -> Z x t
  Undefined _       -> Undefined t
  Code x _          -> Code x t
  Array x _         -> Array x t
  Block x _         -> Block x t
  Tuple x _         -> Tuple x t
  Record x _        -> Record x t
  Index x y _       -> Index x y t
  Lookup x y _      -> Lookup x y t
  TLookup x y _     -> TLookup x y t
  Var x _           -> Var x t
  Function a at b _ -> Function a at b t
  Application f v _ -> Application f v t
  LetBlock bs e'    -> LetBlock bs (updateAnnotation t e')

-- }}}
