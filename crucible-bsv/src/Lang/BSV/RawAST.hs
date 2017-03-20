module Lang.BSV.RawAST where

readParsed :: FilePath -> IO AST
readParsed path = do
  s <- readFile path
  return (read s)

data Kind = KindValue | KindNumeric
  deriving (Eq, Show, Read)

data BlockKind = BlockKindBegin | BlockKindAction | BlockKindActionValue
  deriving (Eq, Show, Read)

data BindingKind = BindingKindNone | BindingKindEq | BindingKindLArrow
  deriving (Eq, Show, Read)

data AstVarInit =
  AstVarInit AST [AST] BindingKind AST
  deriving (Eq, Show, Read)

data AstFunctionProto =
  AstFunctionProto AST AST [AST] [AST]
  deriving (Eq, Show, Read)

type AstIde = AST
type AstNum = AST
type PackageStmt = AST
type AstTypedefDefinee = AST

data AST
  = AstIde String
  | AstAttrInstance [AstIde] [Maybe AST]
  | AstTypeNum Integer
  | AstTypeVar String
  | AstTypeFunction AstFunctionProto
  | AstTypeConstructed String [AST]
  | AstTypedefDefinedAsStruct [AST] [AST]
  | AstTypedefDefinedAsTaggedUnion [AST] [AST]
  | AstTypedefDefinedAsEnum [AstIde] [Maybe Int]
  | AstTypedefDefinee AST [AST] [Kind]
  | AstNum Integer
  | AstString String
  | AstExpr AST [AST]
  | AstCondPredicate [AST]
  | AstCondPattern AST AST
  | AstBlock BlockKind (Maybe AST) [AST]
  | AstReturn AST
  | AstStructExpr AST [AST] [AST]
  | AstTaggedUnionExpr AST (Maybe AST)
  | AstCase AST [AST] [AST]
  | AstPatternCase AST [AST] [AST]
  | AstInterfaceExpr AST [AST]
  | AstVarDecl AST [AstVarInit]
  | AstLet AstIde BindingKind AST
  | AstMatch AST AST
  | AstAssign AST BindingKind AST
  | AstRule AST (Maybe AST) [AST]
  | AstFunctionDef AstFunctionProto [AST] AST
  | AstMethodDef AST AST [AST] [AST] (Maybe AST) AST
  | AstInterfaceDef (Maybe AST) AST [AST]
  | AstInterfaceAssign (Maybe AST) AST AST
  | AstIf AST AST (Maybe AST)
  | AstFor AST AST AST AST
  | AstWhile AST AST
  | AstFSMseq [AST]
  | AstFSMpar [AST]
  | AstFSMif AST AST AST
  | AstFSMfor AST AST AST AST
  | AstFSMwhile AST AST
  | AstFSMrepeat AST AST
  | AstFSMreturn
  | AstFSMbreak
  | AstFSMcontinue
  | AstPatternVarIde AST
  | AstPatternConst AST
  | AstStructPattern AST [AST] [AST]
  | AstTaggedUnionPattern AST (Maybe AST)
  | AstPackage (Maybe AstIde) [PackageStmt]
  | AstImport AstIde
  | AstExport [AstIde] [Bool]
  | AstModuleDef (Maybe AST) AstIde [AST] [AST] AST [AST] [AST]
  | AstImportBDPI AstFunctionProto
  | AstTypedef AstTypedefDefinee AST [AstIde]
  | AstIfcDecl AstTypedefDefinee [AST]
  | AstIfcDeclSubIfcDecl AstIde AST
  | AstIfcDeclMethodDecl AstIde AST [AstIde] [AST]
  | AstInstance AST [AST] [AST] [AST]
  deriving (Eq, Show, Read)
