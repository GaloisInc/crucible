module Lang.BSV.AST where

type Ident = String
type Number = Integer

data Kind
  = KindValue
  | KindNumeric
 deriving (Eq,Ord,Show)

data BlockKind
  = Action
  | Value
  | ActionValue
 deriving (Eq,Ord,Show)

data Binding 
  = BindingEq Expr
  | BindingLArrow Expr
 deriving (Eq,Ord,Show)

data Proviso
  = Proviso Ident [Type]
 deriving (Eq,Ord,Show)

data AttributeInstance
  = AttributeInstance Ident (Maybe Expr)
 deriving (Eq,Ord,Show)

{-
  -- FSM 
  | AstFSM [AST]
  | AstFSMPar [AST]
  | AstFSMIf AST AST AST
  | AstFSMFor AST AST AST AST
  | AstFSMWhile AST AST
  | AstFSMRepeat AST AST
  | AstFSMReturn
  | AstFSMBreak
  | AstFSMContinue
 deriving (Eq,Ord,Show)
-}
-------------------------------------------------------------
-- Expressions

data UnaryOp
  = UOpPlus           --   +
  | UOpMinus          --   -
  | UOpBang           --   !
  | UOpTilde          --   ~
  | UOpAmp            --   &
  | UOpTildeAmp       --   ~&
  | UOpVBar           --   |
  | UOpTildeVBar      --   ~|
  | UOpHat            --   ^
  | UOpHatTilde       --   ^~
  | UOpTildeHat       --   ~^
 deriving (Eq,Ord,Show)

data BinaryOp
  = BinOpStar         --   *
  | BinOpSlash        --   /
  | BinOpPercent      --   %
  | BinOpPlus         --   +
  | BinOpMinus        --   -
  | BinOpLtLt         --   <<
  | BinOpGtGt         --   >>
  | BinOpLtEq         --   <=
  | BinOpGtEq         --   >=
  | BinOpLt           --   <
  | BinOpGt           --   >
  | BinOpEqEq         --   ==
  | BinOpSlashEq      --   /=
  | BinOpAmp          --   &
  | BinOpHat          --   ^
  | BinOpHatTilde     --   ^~
  | BinOpTildeHat     --   ~^
  | BinOpVBar         --   |
  | BinOpAmpAmp       --   &&
  | BinOpVBarVBar     --   ||
 deriving (Eq,Ord,Show)

data Expr
  = ExprCond [CondPredicate] Expr Expr
  | ExprUnaryOp UnaryOp Expr
  | ExprBinaryOp Expr BinaryOp Expr
  | ExprVar Ident
  | ExprProj Expr Ident
  | ExprIntLit Number
  | ExprRealLit Rational
  | ExprStringLit String
  | ExprDon'tCare
  | ExprValueOf Type
  | ExprBitConcat [Expr]
  | ExprBitSelect Expr Expr (Maybe Expr)
  | ExprFunCall Expr [Expr]
  | ExprMethodCall Expr Ident [Expr]
  | ExprTypeAssert Type Expr
  | ExprStruct Ident [(Ident,Expr)]
  | ExprUnion Ident (Either Expr [(Ident,Expr)])
  | ExprBlock [ExprStmt] Expr
--  | ExprInterface Ident [IFaceStmt]
 deriving (Eq,Ord,Show)

data ExprStmt
  = ExprStmtVarDecl [VarDecl]
  | ExprStmtVarAssign VarAssign
  | ExprStmtFunDef FunDef
  | ExprStmtModuleDef ModuleDef
  | ExprStmtBlock [ExprStmt] Expr
  ---- FIXME, more stuff here...
 deriving (Eq,Ord,Show)

data CondPredicate
  = CondExpr Expr
  | CondMatch Expr Pattern
 deriving (Eq,Ord,Show)

-------------------------------------------------------------
-- Patterns

data Pattern
  = PatternVar Ident
  | PatternWildcard
  | PatternConst PatternConst
  | PatternStruct Ident [(Ident,Pattern)]
  | PatternUnion Ident (Maybe Pattern)
  | PatternTuple [Pattern]
 deriving (Eq,Ord,Show)

data PatternConst
  = PatternConstInt Number
  | PatternConstReal Rational
  | PatternConstString String
  | PatternConstIdent Ident
 deriving (Eq,Ord,Show)

-------------------------------------------------------------
-- Variable Declarations

data VarDecl
  = VarDecl Type Ident [Expr] (Maybe Expr)
  | VarDeclArrow Type Ident Expr
  | VarLet Ident Binding
  | VarMatch Pattern Expr
 deriving (Eq,Ord,Show)

-------------------------------------------------------------
-- Types

data Type
  = TypeVar Ident
  | TypeNat Integer
  | TypeBit (Maybe (Integer, Integer))
  | TypeSizeOf [Type]
  | TypeCon Ident [Type]
  | TypeFun FunProto
 deriving (Eq,Ord,Show)

-------------------------------------------------------------
-- Typedefs

data TypeProto
  = TypeProto
  { typedefName    :: Ident
  , typedefFormals :: [(Ident,Kind)]
  }
 deriving (Eq,Ord,Show)

data Typedef
  = TypedefSynonym Type TypeProto
  | TypedefEnum [(Ident,Number)] Ident
  | TypedefStruct [StructMember] TypeProto
  | TypedefUnion  [UnionMember] TypeProto
 deriving (Eq,Ord,Show)

data StructMember
  = StructLeaf     Type Ident
  | StructSubUnion [UnionMember] Ident
 deriving (Eq,Ord,Show)

data UnionMember
  = UnionLeaf      (Maybe Type) Ident
  | UnionSubStruct [StructMember] Ident
  | UnionSubUnion  [UnionMember] Ident
 deriving (Eq,Ord,Show)

--------------------------------------------------------------
-- Rules

data Rule =
  Rule
  { ruleAttributes :: [AttributeInstance]
  , ruleIdent :: Ident
  , ruleCond  :: CondPredicate
  , ruleBody  :: Stmt
  }
 deriving (Eq,Ord,Show)


--------------------------------------------------------------
-- Statement

data Stmt
  = StmtExpr Expr
  | StmtReturn Expr
  | StmtVarDecl [VarDecl]
  | StmtLet Ident Binding
  | StmtVarAssign VarAssign
  | StmtFunDef FunDef
  | StmtModuleDef ModuleDef
  | StmtBlock [Stmt]
  | StmtIf CondPredicate Stmt Stmt
  | StmtCase Expr [CaseItem] (Maybe Stmt)
  | StmtFor [(Maybe Type, Ident, Expr)] -- init
            Expr -- Test
            [(Ident,Expr)] -- incr
            Stmt -- body
  | StmtWhile Expr Stmt
 deriving (Eq,Ord,Show)

data CaseItem
  = CaseItem Pattern [CondPredicate] Stmt
 deriving (Eq,Ord,Show)

data VarAssign
  = VarAssignEq LValue Expr
  | VarAssignArrow Ident Expr
 deriving (Eq,Ord,Show)
  
data LValue
  = LValueIdent Ident
  | LValueField LValue Ident
  | LValueIdx LValue Expr
  | LValueIdxes LValue Expr Expr
 deriving (Eq,Ord,Show)

--------------------------------------------------------------
-- Modules

data ModuleDef
  = ModuleDef
  { moduleType :: Maybe Type
  , moduleName :: Ident
  , moduleFormals :: [([AttributeInstance],Ident,Type)]
  , moduleIfcType :: Ident
  , moduleProvisos :: [Proviso]
  , moduleStmts :: ModuleStmt
  }
 deriving (Eq,Ord,Show)

data ModuleStmt
  = ModuleInst [AttributeInstance] Type Ident ModuleApp
  | ModuleMethodDef MethodDef
  | ModuleInterface InterfaceDef
  | ModuleRule Rule
  | ModuleStmt Stmt
 deriving (Eq,Ord,Show)

data ModuleApp
  = ModuleApp Ident [(ActualKind,Expr)]
 deriving (Eq,Ord,Show)

data ActualKind
  = ActualExpr
  | ActualClockedBy
  | ActualResetBy
 deriving (Eq,Ord,Show)

data InterfaceDef
  = InterfaceDef
  { ifcDefType :: Ident
  , ifcDefName :: Ident
  , ifcDefStmts :: [IfcDefStmt]
  }
 deriving (Eq,Ord,Show)

data IfcDefStmt
  = IfcDefMethod MethodDef
  | IfcDefInterface InterfaceDef
 deriving (Eq,Ord,Show)

data MethodDef
  = MethodDef
  { methodProto   :: MethodProto
  , methodStmts   :: [Stmt]
  }
 deriving (Eq,Ord,Show)


-------------------------------------------------------------
-- Interface Decl

data InterfaceDecl
  = InterfaceDecl
  { ifcAttributeInstances :: [AttributeInstance]
  , ifcTypeProto          :: TypeProto
  , ifcDecls              :: [IfcDeclStmt]
  , ifcTypeName           :: Maybe Ident
  }
 deriving (Eq,Ord,Show)
 
data IfcDeclStmt
  = IfcDeclMethod MethodProto
  | IfcDeclInterface [AttributeInstance] Type Ident
 deriving (Eq,Ord,Show)

data MethodProto
  = MethodProto
  { methodAttributeInstances :: [AttributeInstance]
  , methodResultType         :: Type
  , methodName               :: Ident
  , methodFormals            :: [([AttributeInstance], Type, Ident)]
  }
 deriving (Eq,Ord,Show)

-------------------------------------------------------------
-- Package

newtype ExportStmt
  = ExportStmt [(Ident,Bool)]
 deriving (Eq,Ord,Show)

newtype ImportStmt
  = ImportStmt [Ident]
 deriving (Eq,Ord,Show)

newtype Derive = Derive Ident
 deriving (Eq,Ord,Show)

data PackageStmt
  = PackageIfcDecl InterfaceDecl
  | Typedef Typedef [Derive]
  | ImportBDPI FunProto
  | FunctionDefStmt FunDef
  | ModuleDefStmt ModuleDef
  | PackageVarDecl [VarDecl]
--  | Instance AST [AST] [AST] [AST]

 deriving (Eq,Ord,Show)

data FunDef
  = FunDef
  { funAttributeInstances :: [AttributeInstance]
  , funDefProto           :: FunProto
  , funBody               :: [Stmt]
  }
 deriving (Eq,Ord,Show)

data FunProto
  = FunProto
  { funResultType :: Type
  , funName       :: Ident
  , funFormals    :: [(Type,Ident)]
  , funProvisos   :: [Proviso]
  }
 deriving (Eq,Ord,Show)


data Package
  = Package
  { packageIdent   :: Ident
  , packageExports :: [ExportStmt]
  , packageImports :: [ImportStmt]
  , packageStmts   :: [PackageStmt]
  }
 deriving (Eq,Ord,Show)
