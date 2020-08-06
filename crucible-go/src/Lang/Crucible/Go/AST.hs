{-|
Module      : Lang.Crucible.Go.AST
Description : Go language abstract syntax
Maintainer  : abagnall@galois.com
Stability   : experimental

The type definitions in this file are designed to match the standard
'go/ast' package as closely as possible.
-}
module Lang.Crucible.Go.AST where

import           Data.Text

-- TODO: make fields strict

-- | A Go source file.
data File a =
  File { file_name :: Ident -- ^ package name
       , decls :: [Decl a] -- ^ top-level declarations
       , imports :: [ImportSpecification a] -- ^ imports in this file
       , unresolved :: [Ident] -- ^ unresolved identifiers in this file
       }

data Stmt a =
  BadStmt a -- ^ A BadStmt node is a placeholder for statements
            -- containing syntax errors for which no correct statement
            -- nodes can be created.
  | AssignStmt a (AssignStatement a)
  | BlockStmt a (BlockStatement a)
  | BranchStmt a (BranchStatement a)
  | DeclStmt a (DeclStatement a)
  | DeferStmt a (DeferStatement a)
  | EmptyStmt a EmptyStatement
  | ExprStmt a (ExprStatement a)
  | ForStmt a (ForStatement a)
  | GoStmt a (GoStatement a)
  | IfStmt a (IfStatement a)
  | IncDecStmt a (IncDecStatement a)
  | LabeledStmt a (LabeledStatement a)
  | RangeStmt a (RangeStatement a)
  | ReturnStmt a (ReturnStatement a)
  | SelectStmt a (SelectStatement a)
  | SendStmt a (SendStatement a)
  | SwitchStmt a (SwitchStatement a)
  | TypeSwitchStmt a (TypeSwitchStatement a)

data Expr a =
  BadExpr a -- ^ A BadExpr node is a placeholder for expressions
            -- containing syntax errors for which no correct
            -- expression nodes can be created.
  | BasicLitExpr a BasicLit
  | BinaryExpr a (BinaryExpression a)
  | CallExpr a (CallExpression a)
  | CompositeLitExpr a (CompositeLit a)
  | IdentExpr a Ident
  | EllipsisExpr a (Ellipsis a)
  | FuncLitExpr a (FuncLit a)
  | IndexExpr a (IndexExpression a)
  | KeyValueExpr a (KeyValueExpression a)
  | ParenExpr a (ParenExpression a)
  | SelectorExpr a (SelectorExpression a)
  | SliceExpr a (SliceExpression a)
  | StarExpr a (StarExpression a)
  | TypeAssertExpr a (TypeAssertExpression a)
  | UnaryExpr a (UnaryExpression a)
  -- type expressions
  | ArrayTypeExpr a (ArrayType a)
  | FuncTypeExpr a (FuncType a)
  | InterfaceTypeExpr a (InterfaceType a)
  | MapTypeExpr a (MapType a)
  | StructTypeExpr a (StructType a)

-- ^ Statement record types.

-- | An assignment or a short variable declaration.
data AssignStatement a =
  AssignStatement
  { assign_lhs :: [Expr a]
  , assign_rhs :: [Expr a]
  }

-- | A braced statement list.
data BlockStatement a =
  BlockStatement
  { block_stmts :: [Stmt a]
  }

-- | A break, continue, goto, or fallthrough statement.
data BranchStatement a =
  BranchStatement
  { branch_tok :: BranchToken
  , branch_label :: Maybe Ident
  }

-- | A declaration in a statement list.
data DeclStatement a =
  DeclStatement
  { decl :: Decl a
  }

-- | A defer statement.
data DeferStatement a =
  DeferStatement
  { defer_call :: CallExpression a
  }

-- | An empty statement.
data EmptyStatement =
  EmptyStatement
  { empty_implicit :: Bool -- ^ if set, ";" was omitted in the source
  }

-- | A (stand-alone) expression in a statement list.
data ExprStatement a =
  ExprStatement
  { stmt_expr :: Expr a
  }

-- | A for statement.
data ForStatement a =
  ForStatement
  { for_init :: Maybe (Stmt a) -- ^ initialization statement; or nil
  , for_cond :: Maybe (Stmt a) -- ^ condition; or nil
  , for_post :: Maybe (Stmt a) -- ^ post iteration statement; or nil
  , for_body :: BlockStatement a
  }

-- | A go statement.
data GoStatement a =
  GoStatement
  { go_call :: CallExpression a
  }

-- | An if statement.
data IfStatement a =
  IfStatement
  { if_init :: Maybe (Stmt a) -- ^ intiialization statement; or nil
  , if_cond :: Expr a -- ^ condition
  , if_body :: BlockStatement a
  , if_else :: Maybe (Stmt a) -- ^ else_branch; or nil
  }

-- | An increment or decrement statement.
data IncDecStatement a =
  IncDecStatement
  { incdec_x :: Expr a
  , inc :: Bool -- ^ true if increment, false if decrement
  }

-- | A labeled statement.
data LabeledStatement a =
  LabeledStatement
  { stmt_label :: Ident
  , labeled_stmt :: Stmt a
  }

-- | A for statement with a range clause.
data RangeStatement a =
  RangeStatement
  { range_key :: Maybe (Expr a)
  , range_value :: Maybe (Expr a)
  , range_x :: Expr a -- ^ value to range over
  , range_body :: BlockStatement a
  }

-- | A return statement.
data ReturnStatement a =
  ReturnStatement
  { return_results :: [Expr a] -- ^ result expressions
  }

-- | A select statement.
data SelectStatement a =
  SelectStatement
  { select_body :: BlockStatement a -- ^ CommClauses only
  }

-- | A send statement.
data SendStatement a =
  SendStatement
  { send_chan :: Expr a
  , send_value :: Expr a }

-- | An expression switch statement.
data SwitchStatement a =
  SwitchStatement
  { switch_init :: Maybe (Stmt a) -- ^ initialization statement; or nil
  , switch_tag :: Maybe (Expr a) -- ^ tag expression; or nil
  , switch_body :: BlockStatement a -- ^ CaseClauses only
  }

-- | A type switch statement.
data TypeSwitchStatement a =
  TypeSwitchStatement
  { typeswitch_init :: Maybe (Stmt a) -- ^ initialization statement; or nil
  , typeswitch_assign :: Stmt a -- ^ x := y.(type) or y.(type)
  , typeswitch_body :: BlockStatement a -- ^ CaseClauses only
  }

data Decl a =
  -- | A BadDecl node is a placeholder for declarations containing
  -- syntax errors for which no correct declaration nodes can be
  -- created.
  BadDecl a
  | FuncDecl a (FuncDeclaration a)
  | GenDecl a (GenDeclaration a)

-- | A function declaration.
data FuncDeclaration a =
  FuncDeclaration
  { recv :: Maybe (FieldList a) -- ^ receiver (methods); or nil (functions)
  , func_name :: Ident -- ^ function/method name
  , func_type :: FuncType a -- ^ function signature
  , func_body :: BlockStatement a -- ^ function body; or nil for
                                  -- external (non-Go) function
  }

-- | (generic declaration node) An import, constant, type or variable
-- declaration.
data GenDeclaration a =
  GenDeclaration
  { specs :: [Spec a]
  }

data Spec a =
  ImportSpec a (ImportSpecification a)
  | ConstSpec a (ValueSpecification a)
  | TypeSpec a (TypeSpecification a)
  | VarSpec a (ValueSpecification a)

-- | A single package import.
data ImportSpecification a =
  ImportSpecification
  { import_name :: Maybe Ident -- ^ local package name (including "."); or nil
  , import_path :: BasicLit }

-- | A constant or variable declaration (ConstSpec or VarSpec production).
data ValueSpecification a =
  ValueSpecification
  { valuespec_names :: [Ident] -- ^ value names (nonempty)
  , valuespec_type :: Maybe (Expr a) -- ^ value type; or nil
  , valuespec_values :: [Expr a] -- ^ initial values
  }

-- | A type declaration (TypeSpec production).
data TypeSpecification a =
  TypeSpecification
  { typespec_name :: Ident -- ^ type name
  , typespec_type :: Expr a -- ^ IdentExpr, ParenExpr, SelectorExpr,
                            -- ^ StarExpr, or any xxxTypeExpr
  }
  
-- | An array or slice type. 
data ArrayType a =
  ArrayTy
  { len :: Maybe (Either Int (Ellipsis a)) -- ^ Ellipsis node for
                                           -- [...]T array types, nil
                                           -- for slice types
  , array_elt :: Expr a -- ^ element type
  }

-- | A function type.
data FuncType a =
  FuncType
  { params :: FieldList a -- ^ (incoming) parameters
  , results :: FieldList a -- ^ (outgoing) results
  }

-- | An interface type.
data InterfaceType a =
  InterfaceType
  { interface_methods :: FieldList a -- ^ list of methods
  , interface_incompete :: Bool -- ^ true if (source) methods are
                                -- missing in the methods list
  }

-- | A map type.
data MapType a =
  MapType
  { map_key :: Expr a -- ^ key type
  , map_value :: Expr a -- ^ value type
  }

-- | A struct type.
data StructType a =
  StructType
  { struct_fields :: FieldList a -- ^ list of field declarations
  , struct_incomplete :: Bool -- ^ true if (source) fields are missing
                              -- in the Fields list
  } 

-- | A binary expression.
data BinaryExpression a =
  BinaryExpression
  { x :: Expr a -- ^ left operand
  , op :: BinaryOp -- ^ operator
  , y :: Expr a -- ^ right operand
  }

-- | An expression followed by an argument list.
data CallExpression a =
  CallExpression
  { fun :: Expr a -- ^ function expression
  , args :: [Expr a] -- ^ function arguments
  }

-- | An expression followed by an index.
data IndexExpression a =
  IndexExpression
  { index_x :: Expr a -- ^ expression
  , index_ix :: Expr a -- ^ index expression
  }

-- | (key : value) pairs in composite literals.
data KeyValueExpression a =
  KeyValueExpression
  { kv_key :: Expr a
  , kv_value :: Expr a
  }

-- | A parenthesized expression.
data ParenExpression a =
  ParenExpression
  { paren_x :: Expr a -- ^ parenthesized expression
  }

-- | An expression followed by a selector.
data SelectorExpression a =
  SelectorExpression
  { selector_x :: Expr a -- ^ expression
  , selector_sel :: Ident -- ^ field selector
  }

-- | An expression followed by slice indices.
data SliceExpression a =
  SliceExpression
  { slice_x :: Expr a -- ^ expression
  , slice_low :: Maybe (Expr a) -- ^ begin of slice range; or nil
  , slice_high :: Maybe (Expr a) -- ^ end of slice range; or nil
  , slice_max :: Maybe (Expr a) -- ^ maximum capacity of slice; or nil
  , slice3 :: Bool -- ^ true if 3-index slice (2 colons present)
  }

-- | An expression of the form "*" Expression. Semantically it could
-- be a unary "*" expression, or a pointer type.
data StarExpression a =
  StarExpression
  { star_x :: Expr a -- ^ operand
  }

-- | An expression followed by a type assertion.
data TypeAssertExpression a =
  TypeAssertExpression
  { typeassert_x :: Expr a -- ^ expression
  , typeassert_type :: Maybe (Expr a) -- ^ asserted type; nil means
                                      -- type switch X.(type)
  }

-- | A unary expression. Unary "*" expressions are represented via
-- StarExpr nodes.
data UnaryExpression a =
  UnaryExpression
  { unary_op :: UnaryOp -- ^ operator
  , unary_x :: Expr a -- ^ operand
  }

data BasicLitType =
  LiteralInt
  | LiteralFloat
  | LiteralImag
  | LiteralChar
  | LiteralString

-- | A literal of basic type. 
data BasicLit =
  BasicLit
  BasicLitType -- ^ "kind" of the literal
  Text         -- ^ literal value as a string

-- | A function literal.
data FuncLit a =
  FuncLit
  { funclit_type :: Expr a -- ^ function type
  , funclit_body :: BlockStatement a -- ^ function body
  }

data BinaryOp =
  BinaryOp -- TODO
  
data UnaryOp =
  UnaryOp -- TODO

data BranchToken =
  Break
  | Continue
  | Goto
  | Fallthrough

-- | An identifier.
data Ident =
  Ident Text

-- | A case of an expression or type switch statement.
data CaseClause a =
  CaseClause
  { list :: [Expr a] -- ^ list of expressions of types; nil means default case
  , case_body :: [Stmt a] -- ^ statement list
  }

-- Leave out channel stuff for now.
-- -- | The direction of a channel type is indicated by a bit mask
-- -- including one or both of the following constants.
-- newtype ChanDir = ChanDir { unChanDir :: Integer }

-- -- | A ChanType node represents a channel type.
-- data ChanType a =
--   ChanType { chantype_dir :: ChanDir -- channel direction
--            , chantype_value :: Expr a -- value type
--            }

-- | A case of a select statement.
data CommClause a =
  CommClause
  { comm :: Maybe (Stmt a) -- ^ send or receive statement; nil means
                           -- default case
  , comm_body :: [Stmt a] -- ^ statement list
  }

-- | A composite literal.
data CompositeLit a =
  CompositeLit
  { composite_type :: Maybe (Expr a) -- ^ literal type; or nil
  , composite_elts :: [Expr a] -- ^ list of composite elements
  , incompose :: Bool -- ^ true if (source) expressions are missing in
                      -- the expr list
  }

-- | An Ellipsis node stands for the "..." type in a parameter list or
-- the "..." length in an array type.
data Ellipsis a =
  Ellipsis
  { ellipsis_elt :: Maybe (Expr a) -- ^ ellipsis element type
                                   -- (parameter lists only); or nil
  }

-- | A Field represents a Field declaration list in a struct type, a
-- method list in an interface type, or a parameter/result declaration
-- in a signature. Field.Names is nil for unnamed parameters
-- (parameter lists which only contain types) and embedded struct
-- fields. In the latter case, the field name is the type name.
data Field a =
  Field
  { field_names :: Maybe [Ident] -- ^ field/method/parameter names; or nil
  , field_type :: Expr a -- ^ field/method/parameter type
  , field_tag :: Maybe BasicLit -- ^ field tag; or nil
  }

-- | A FieldList represents a list of Fields, enclosed by parentheses
-- or braces.
data FieldList a =
  FieldList
  { field_list :: [Field a]
  }


-- Don't need the following things for now.

-- TODO: Node?

-- data Scope =
--   Scope { scope_outer :: Maybe Scope
--         , scope_objects :: map string object

-- -- TODO: is this right?
-- data Object a =
--   BadObject
--   | PackageObject (Package a)
--   | ConstantObject (Expr a)
--   | TypeObject (Expr a)
--   | VariableObject (Expr a)
--   | FunctionObject (Expr a)
--   | LabelObject (Expr a)

-- data Package a =
--   Package { package_name :: Text -- package name
--           , package_scope :: Scope -- package scope across all files
--           , package_imports 
