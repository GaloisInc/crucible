module Main where

--import           Control.Exception
import           Control.Monad
import           Control.Monad.ST

import           Lang.BSV.AST
import           Lang.BSV.TransAST

import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle

import           Lang.Crucible.BSV.Analysis
import           Lang.Crucible.BSV.Translation

import AES_Defs

integerType :: Type
integerType = TypeCon "Integer" []

intType :: Integer -> Type
intType n = TypeCon "Int" [TypeNat n]

uintType :: Integer -> Type
uintType n = TypeCon "UInt" [TypeNat n]

bitType :: Integer -> Type
bitType n = TypeCon "Bit" [TypeNat n]

boolType :: Type
boolType = TypeCon "Bool" []


testFun :: FunDef
testFun =
  let tp = integerType in
  FunDef
  { funAttributeInstances = []
  , funDefProto =
    FunProto
    { funResultType = boolType
    , funName       = "testFun"
    , funFormals    = [(tp, "x"), (tp, "y")]
    , funProvisos   = []
    }
  , funBody =
    [ StmtExpr $
         ExprBinaryOp (ExprVar "x") BinOpSlashEq
          (ExprBinaryOp (ExprVar "y") BinOpPlus (ExprIntLit 10))
    ]
  }

main :: IO ()
main = do
  let (Just res, errs) = trans aesDefs
  unless (null errs) $ do
     putStrLn "Errors!"
     putStrLn "================="
     mapM_ putStrLn errs
     putStrLn "================="
  let tenv = processTypedefs (packageStmts res) initialTypeEnv
  cfgs <- withHandleAllocator $ \halloc -> stToIO $ do
            venv0 <- initialValEnv halloc
            (_venv,cfgs) <- translatePackageFuns halloc tenv venv0 (packageStmts res)
            return cfgs
  mapM_ (\(AnyCFG cfg) ->
             do putStrLn "=============="
                print (cfgHandle cfg)
                print cfg)
        cfgs



--main =
 -- withHandleAllocator $ \halloc -> do
 --   AnyCFG g <- stToIO (translateFun halloc emptyTypeEnv testFun)
 --   print g


  -- interact $ \input ->
  --   let raw = read input
  --       ast = transPackage raw
  --    in show ast

