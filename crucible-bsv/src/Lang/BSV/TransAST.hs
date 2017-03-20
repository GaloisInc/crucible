{-# LANGUAGE FlexibleContexts #-}

module Lang.BSV.TransAST where

import           Control.Monad.Writer
import           Control.Monad.Trans.Maybe
import           Data.Foldable
import           Data.Maybe
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Lang.BSV.AST
import qualified Lang.BSV.RawAST as R

type Trans = MaybeT (Writer (Seq String))

zipFail :: String -> [a] -> [b] -> Trans [(a,b)]
zipFail msg = go Seq.empty
 where
  go xs [] [] = return (toList xs)
  go xs (a:as) (b:bs) = go (xs Seq.|> (a,b)) as bs
  go xs _ _ = do tell (Seq.singleton ("Zip with incompatible lengths in " ++ msg))
                 return (toList xs)

orElse :: a
       -> Trans a
       -> Trans a
orElse x m = MaybeT (return . Just . fromMaybe x =<< runMaybeT m)

transListOf :: (a -> Trans b)
            -> [a]
            -> Trans [b]
transListOf f = go Seq.empty
 where
  go bs [] = return (toList bs)
  go bs (a:as) =
    do bs' <- orElse bs $ do
                 b <- f a
                 return (bs Seq.|> b)
       go bs' as       

asIdent :: R.AST -> Trans Ident
asIdent (R.AstIde nm) = return nm
asIdent _ = giveUp "Expected identifier"

asIdents :: [R.AST] -> Trans [Ident]
asIdents = mapM asIdent

trans :: R.AST -> (Maybe Package, [String])
trans ast =
  let (res, errs) = runWriter . runMaybeT . transPackage $ ast
   in (res, toList errs)

transPackage :: R.AST -> Trans Package
transPackage ast = case ast of
  R.AstPackage mnm sts0 -> do
      goExports mnm Seq.empty sts0
  _ ->
      giveUp $ unwords ["Expected package:", show ast]

 where
  build mnm ex im sts = do
    nm <- case mnm of
            Just (R.AstIde nm) -> return nm
            _ -> do reportError "Package missing name"
                    return ""
    return $ Package
             { packageIdent   = nm
             , packageExports = toList ex
             , packageImports = toList im
             , packageStmts   = toList sts
             }

  goExports mnm ex (R.AstExport nms bs:ss) = do
      ex' <- orElse ex $ do
              nms' <- asIdents nms
              x <- ExportStmt <$> zipFail "export list" nms' bs
              return (ex Seq.|> x)
      goExports mnm ex' ss
  goExports mnm ex ss =
      goImports mnm ex Seq.empty ss

  goImports mnm ex im (R.AstImport nm : ss) =  do
      im' <- orElse im $ do
               nm' <- asIdent nm
               return (im Seq.|> ImportStmt [nm'])
      goImports mnm ex im' ss
  goImports mnm ex im ss =
      goStmts mnm ex im Seq.empty ss

  goStmts mnm ex im psts (s:ss) = do
      psts' <- orElse psts $ do
                 p <- goStmt s
                 return (psts Seq.|> p)
      goStmts mnm ex im psts' ss
  goStmts mnm ex im psts [] =
      build mnm ex im psts

  goStmt s = case s of
    R.AstIfcDecl proto body -> PackageIfcDecl <$> transIfaceDecl proto body
    R.AstTypedef typeProto defn derives ->
       do typeProto' <- transTypeProto typeProto
          td <- transTypedef defn typeProto'
          derives' <- map Derive <$> asIdents derives
          return (Typedef td derives')
    R.AstVarDecl tp decls ->
       do tp' <- transType tp
          PackageVarDecl <$> transListOf (transVarDecl tp') decls
    R.AstFunctionDef proto provisos body ->
       do proto' <- transFunProto proto
          provisos' <- transListOf transProviso provisos
          body' <- transFunBody body
          return $ FunctionDefStmt
                 $ FunDef
                   { funAttributeInstances = [] -- FIXME??
                   , funDefProto = proto'{ funProvisos = provisos' }
                   , funBody = body'
                   }

    _ -> giveUp $ "Unexpected package statmenmt:" ++ show s

translateKind :: R.Kind
              -> Trans Kind
translateKind R.KindValue = return KindValue
translateKind R.KindNumeric = return KindNumeric


transStmt :: R.AST
          -> Trans Stmt
transStmt s = case s of
  R.AstVarDecl tp vd ->
     do tp' <- transType tp
        StmtVarDecl <$> transListOf (transVarDecl tp') vd
  R.AstLet nm knd ex -> StmtLet <$> asIdent nm <*> transBinding knd ex
  R.AstReturn ex -> StmtReturn <$> transExpr ex
  R.AstFor init test incr body ->
       do init' <- transForInit init
          test' <- transExpr test
          incr' <- transForIncr incr
          body' <- transStmt body
          return $ StmtFor init' test' incr' body'
  R.AstBlock R.BlockKindBegin _nm stmts ->
       StmtBlock <$> mapM transStmt stmts
  R.AstAssign lhs R.BindingKindEq rhs ->
       do lhs' <- transLValue lhs
          rhs' <- transExpr rhs
          return $ StmtVarAssign $ VarAssignEq lhs' rhs'
  R.AstAssign lhs R.BindingKindLArrow rhs ->
       do nm   <- asIdent lhs
          rhs' <- transExpr rhs
          return $ StmtVarAssign $ VarAssignArrow nm rhs'

  _ -> giveUp ("transStmt: unexpected statement form: " ++ show s)


transLValue :: R.AST
            -> Trans LValue
transLValue (R.AstIde nm) =
     return $ LValueIdent nm
transLValue (R.AstExpr (R.AstIde "PrimIndex") [lhs,idx]) =
  do lhs' <- transLValue lhs
     idx' <- transExpr idx
     return $ LValueIdx lhs' idx'
transLValue x = 
     giveUp $ "unexpected LHS: " ++ show x

transForInit :: R.AST
             -> Trans  [(Maybe Type, Ident, Expr)]
transForInit (R.AstVarDecl tp decls) =
  do tp' <- transType tp
     mapM (go tp') decls
 where
  go tp' (R.AstVarInit nm [] R.BindingKindEq ex) =
      do nm' <- asIdent nm
         ex' <- transExpr ex
         return (Just tp', nm', ex')
  go _ x = giveUp $ "transForInit: expected = init: " ++ show x

transForInit x = giveUp $ "transForInit: expected var init: " ++ show x

transForIncr :: R.AST
             -> Trans  [(Ident, Expr)]
transForIncr (R.AstAssign nm R.BindingKindEq ex) =
  do nm' <- asIdent nm
     ex' <- transExpr ex
     return [(nm',ex')]     
transForIncr x =
  giveUp $ "transForIncr: expected var assignment: " ++ show x


transVarDecl :: Type
             -> R.AstVarInit
             -> Trans VarDecl
transVarDecl tp (R.AstVarInit nm idxes knd ex) =
  do nm' <- asIdent nm
     idxes' <- transListOf transExpr idxes
     case knd of
       R.BindingKindNone ->
         return $ VarDecl tp nm' idxes' Nothing
       R.BindingKindEq ->
         do ex' <- transExpr ex
            return $ VarDecl tp nm' idxes' (Just ex')
       R.BindingKindLArrow -> 
         do unless (null idxes) (giveUp "illegal array dims on <- var decl")
            ex' <- transExpr ex
            return $ VarDeclArrow tp nm' ex'


transBinding :: R.BindingKind
             -> R.AST
             -> Trans Binding
transBinding knd ex = case knd of
  R.BindingKindNone -> giveUp "'none' binding kind not allowed"
  R.BindingKindEq -> BindingEq <$> transExpr ex
  R.BindingKindLArrow -> BindingLArrow <$> transExpr ex

transExpr :: R.AST
          -> Trans Expr
transExpr x = case x of
  R.AstNum x ->
     return $ ExprIntLit x
  R.AstIde n ->
     return $ ExprVar n
  R.AstExpr e0 es ->
     do e0' <- transExpr e0
        es' <- transListOf transExpr es
        return $ ExprFunCall e0' es'

  _ -> giveUp ("unexpected expression form " ++ show x)


transFunBody :: R.AST
             -> Trans [Stmt]
transFunBody (R.AstBlock R.BlockKindBegin _ ss) = transListOf transStmt ss
transFunBody x =
  do x' <- transExpr x
     return [StmtReturn x']


transProviso :: R.AST
             -> Trans Proviso
transProviso _ = giveUp "FIXME: implement transProviso"


transTypeProto :: R.AST
               -> Trans TypeProto
transTypeProto (R.AstTypedefDefinee nm fs ks) =
  do nm' <- asIdent nm
     fs' <- asIdents fs
     ks' <- transListOf translateKind ks
     xs <- zipFail "typedef formals" fs' ks'
     return $ TypeProto
              { typedefName = nm'
              , typedefFormals = xs
              }
transTypeProto ast = giveUp $ unwords ["Expected typedef prototype:", show ast]

transTypedef :: R.AST
             -> TypeProto
             -> Trans Typedef
transTypedef (R.AstTypedefDefinedAsStruct _fs _tys) _proto = giveUp "FIXME implement transTypedef for structs" 
transTypedef (R.AstTypedefDefinedAsTaggedUnion _fs _tys) _proto = giveUp "FIXME implement transTypedef for unions" 
transTypedef (R.AstTypedefDefinedAsEnum _fs _vs) _proto = giveUp "FIXME implement transTypedef for enums"
transTypedef tp proto =
  do tp' <- transType tp
     return $ TypedefSynonym tp' proto


transType :: R.AST
          -> Trans Type
transType (R.AstTypeNum n) = return $ TypeNat n
transType (R.AstTypeVar v) = return $ TypeVar v
transType (R.AstTypeFunction p) = TypeFun <$> transFunProto p
transType (R.AstTypeConstructed nm tys) = TypeCon nm <$> transListOf transType tys

transType t = giveUp $ unwords ["Expected type", show t]


transFunProto :: R.AstFunctionProto
              -> Trans FunProto
transFunProto (R.AstFunctionProto retTy nm argIds argTys) =
  do retTy' <- transType retTy
     nm' <- asIdent nm
     xs <- join (zipFail "function prototype" <$> transListOf transType argTys <*> asIdents argIds)
     return FunProto
            { funResultType = retTy'
            , funName       = nm'
            , funFormals    = xs
            , funProvisos   = [] -- FIXME??
            }

reportError :: String -> Trans ()
reportError = tell . Seq.singleton

giveUp :: String -> Trans a
giveUp msg = reportError msg >> mzero


transIfaceDecl :: R.AST -> [R.AST] -> Trans InterfaceDecl
transIfaceDecl _ _ = giveUp "FIXME: implement transIfaceDecl"