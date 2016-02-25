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
       , Pattern(..)
       , Stmt(..)
       , DeclGroup(..)
       , Decl(..)
       , Context(..)
       , Type(..), TypeIndex
       , TyCon(..)
       , Schema(..)
       , toLName
       , tMono, tForall, tTuple, tRecord, tArray, tFun
       , tString, tTerm, tType, tBool, tInt, tAIG
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

import qualified Cryptol.Parser.AST as P (ImportSpec(..), ModName)
import qualified Cryptol.Utils.Ident as P (unpackIdent, unpackModName)

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
  = Bool Bool
  | String String
  | Int Integer
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
  | Function Pattern Expr
  | Application Expr Expr
  -- Sugar
  | Let DeclGroup Expr
  | TSig Expr Type
  | IfThenElse Expr Expr Expr
  deriving (Eq, Show)

data Pattern
  = PWild (Maybe Type)
  | PVar LName (Maybe Type)
  | PTuple [Pattern]
  deriving (Eq, Show)

data Stmt
  = StmtBind     Pattern (Maybe Type) Expr
  | StmtLet      DeclGroup
  | StmtCode     (Located String)
  | StmtImport   Import
  deriving (Eq, Show)

data DeclGroup
  = Recursive [Decl]
  | NonRecursive Decl
  deriving (Eq, Show)

data Decl
  = Decl { dPat :: Pattern, dType :: Maybe Schema, dDef :: Expr }
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
  | IntCon
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
  pretty expr0 = case expr0 of
    Bool b   -> PP.text $ show b
    String s -> PP.dquotes (PP.text s)
    Int i    -> PP.integer i
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
    Function pat expr ->
      PP.text "\\" PP.<+> PP.pretty pat PP.<+> PP.text "-> " PP.<+> PP.pretty expr
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
    IfThenElse e1 e2 e3 ->
      PP.text "if" PP.<+> PP.pretty e1 PP.<+>
      PP.text "then" PP.<+> PP.pretty e2 PP.<+>
      PP.text "else" PP.<+> PP.pretty e3

instance Pretty Pattern where
  pretty pat = case pat of
    PWild mType ->
      prettyMaybeTypedArg ("_", mType)
    PVar (Located name _ _) mType ->
      prettyMaybeTypedArg (name, mType)
    PTuple pats ->
      PP.tupled (map PP.pretty pats)

instance Pretty Stmt where
   pretty = \case

      StmtBind (PVar (Located "" _ _) _leftType) _rightType expr ->
         PP.pretty expr
      StmtBind pat _rightType expr ->
         PP.pretty pat PP.<+> PP.text "<-" PP.<+> PP.align (PP.pretty expr)
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
            Right modName ->
               ppModName modName) PP.<>
         (case iAs of
            Just modName ->
               PP.space PP.<> PP.text "as" PP.<+> ppModName modName
            Nothing -> PP.empty) PP.<>
         (case iSpec of
            Just (P.Hiding names) ->
               PP.space PP.<> PP.text "hiding" PP.<+> PP.tupled (map ppIdent names)
            Just (P.Only names) ->
               PP.space PP.<> PP.tupled (map ppIdent names)
            Nothing -> PP.empty)
      --expr -> PP.cyan . PP.text $ show expr

      where
        ppModName mn = PP.text (intercalate "." (P.unpackModName mn))
        ppIdent i = PP.text (P.unpackIdent i)
        --ppName n = ppIdent (P.nameIdent n)

prettyDef :: Decl -> PP.Doc
prettyDef (Decl pat _ def) =
   PP.pretty pat PP.<+>
   let (args, body) = dissectLambda def
   in (if not (null args)
          then PP.hsep (map PP.pretty args) PP.<> PP.space
          else PP.empty) PP.<>
      PP.text "=" PP.<+> PP.pretty body

prettyMaybeTypedArg :: (Name,Maybe Type) -> PP.Doc
prettyMaybeTypedArg (name,Nothing) =
   PP.text name
prettyMaybeTypedArg (name,Just typ) =
   PP.parens $ PP.text name PP.<+> PP.colon PP.<+> pretty 0 typ

dissectLambda :: Expr -> ([Pattern], Expr)
dissectLambda = \case
  Function pat (dissectLambda -> (pats, expr)) -> (pat : pats, expr)
  expr -> ([], expr)

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
    BoolCon        -> PP.text "Bool"
    IntCon         -> PP.text "Int"
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

tInt :: Type
tInt = TyCon IntCon []

tBlock :: Type -> Type -> Type
tBlock c t = TyCon BlockCon [c,t]

tContext :: Context -> Type
tContext c = TyCon (ContextCon c) []

tVar :: Name -> Type
tVar n = TyVar n

-- }}}
