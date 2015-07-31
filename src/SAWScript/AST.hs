{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
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

       , PrettyPrint(..), pShow, commaSepAll, prettyWholeModule
       ) where

import SAWScript.Token
import SAWScript.Utils

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
#endif
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.PrettyPrint.ANSI.Leijen (Pretty)

import qualified Cryptol.Parser.AST as P (ImportSpec(..), ModName(..), Name(..))

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

prettyWholeModule :: [Stmt] -> PP.Doc
prettyWholeModule = (PP.<> PP.linebreak) . vcatWithSemi . map PP.pretty

vcatWithSemi :: [PP.Doc] -> PP.Doc
vcatWithSemi = PP.vcat . map (PP.<> PP.semi)

instance Pretty Expr where
   pretty = \case
      Bit b    -> PP.text $ show b
      String s -> PP.dquotes (PP.text s)
      Z i      -> PP.integer i
      Code ls  -> PP.braces . PP.braces $ PP.text (getVal ls)
      CType (Located string _ _) -> PP.braces . PP.text $ "|" ++ string ++ "|"
      Array xs -> PP.list (map PP.pretty xs)
      Block stmts ->
         PP.text "do" PP.<+> PP.lbrace PP.<> PP.linebreak PP.<>
         (PP.indent 3 $ (PP.align . vcatWithSemi . map PP.pretty $ stmts)) PP.<> 
         PP.linebreak PP.<> PP.rbrace
      Tuple exprs -> PP.tupled (map PP.pretty exprs)
      Record mapping ->
         PP.braces . (PP.space PP.<>) . (PP.<> PP.space) . PP.align . PP.sep . PP.punctuate PP.comma $
            map (\(name, value) -> PP.text name PP.<+> PP.text "=" PP.<+> PP.pretty value)
                (Map.assocs mapping)
      Index _ _ -> error "No concrete syntax for AST node 'Index'"
      Lookup expr name -> PP.pretty expr PP.<> PP.dot PP.<> PP.text name
      TLookup expr int -> PP.pretty expr PP.<> PP.dot PP.<> PP.integer int
      Var (Located name _ _) ->
         PP.text name
      Function (Located name _ _) mType expr ->
         PP.text "\\" PP.<+> prettyMaybeTypedArg (name,mType) PP.<+> PP.text "-> " PP.<+> PP.pretty expr
      Application f a -> PP.pretty f PP.<+> PP.pretty a
      Let (NonRecursive decl) expr ->
         PP.text "let" PP.<+> 
         prettyDef decl PP.</>
         PP.text "in" PP.<+> PP.pretty expr
      Let (Recursive decls) expr ->
         PP.text "let" PP.<+> 
         PP.cat (PP.punctuate
            (PP.empty PP.</> PP.text "and" PP.<> PP.space)
            (map prettyDef decls)) PP.</>
         PP.text "in" PP.<+> PP.pretty expr
      TSig expr typ -> PP.parens $ PP.pretty expr PP.<+> PP.colon PP.<+> pretty 0 typ

instance Pretty Stmt where
   pretty = \case
      StmtBind (Just (Located name _ _)) leftType _rightType expr ->
         prettyMaybeTypedArg (name,leftType) PP.<+> PP.text "<-" PP.<+> PP.align (PP.pretty expr)
      StmtBind Nothing _leftType _rightType expr ->
         PP.pretty expr
      StmtLet (NonRecursive decl) ->
         PP.text "let" PP.<+> prettyDef decl
      StmtLet (Recursive decls) ->
         PP.text "rec" PP.<+> 
         PP.cat (PP.punctuate
            (PP.empty PP.</> PP.text "and" PP.<> PP.space)
            (map prettyDef decls))
      StmtCode (Located code _ _) ->
         PP.text "let" PP.<+>
            (PP.braces . PP.braces $ PP.text code)
      StmtImport Import{iModule,iAs,iSpec} ->
         PP.text "import" PP.<+>
         (case iModule of
            Left filepath ->
               PP.dquotes . PP.text $ filepath
            Right (P.ModName modPath) ->
               PP.text (intercalate "." modPath)) PP.<>
         (case iAs of
            Just (P.ModName modPath) ->
               PP.space PP.<> PP.text "as" PP.<+> PP.text (intercalate "." modPath)
            Nothing -> PP.empty) PP.<>
         (case iSpec of
            Just (P.Hiding names) ->
               PP.space PP.<> PP.text "hiding" PP.<+> PP.tupled (map stringName names)
            Just (P.Only names) ->
               PP.space PP.<> PP.tupled (map stringName names)
            Nothing -> PP.empty)
      --expr -> PP.cyan . PP.text $ show expr
   
      where
         stringName = \case
            P.Name n       -> PP.text n
            P.NewName _ _i -> error "Encountered 'NewName' while pretty-printing."

prettyDef :: Decl -> PP.Doc
prettyDef Decl{dName,dDef} =
   PP.text (getVal dName) PP.<+>
   let (args, body) = dissectLambda dDef
   in (if not (null args)
          then PP.hsep (map prettyMaybeTypedArg args) PP.<> PP.space
          else PP.empty) PP.<>
      PP.text "=" PP.<+> PP.pretty body

prettyMaybeTypedArg :: (Name,Maybe Type) -> PP.Doc
prettyMaybeTypedArg (name,Nothing) =
   PP.text name
prettyMaybeTypedArg (name,Just typ) =
   PP.parens $ PP.text name PP.<+> PP.colon PP.<+> pretty 0 typ

dissectLambda :: Expr -> ([(Name,Maybe Type)],Expr)
dissectLambda = \case
   Function (Located name _ _) mType
            (dissectLambda -> (names, expr)) ->
               ((name, mType) : names, expr)
   expr -> ([],expr)

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
