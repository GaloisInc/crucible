module SAWScript.AST where

import Data.List

type BitField = [Bool]

data Expr =
    BitLiteral BitField
  | Binder String Expr
  | Bag [Expr]

instance Show Expr where
  show (BitLiteral bools) = "'" ++ (map (\b -> if b then '1' else '0') bools)
  show (Binder name val)  = name ++ " = " ++ (show val)
  show (Bag exprs)        = "{ " ++ (intercalate "; " (map show exprs)) ++ " }"

reflect :: Expr -> String
reflect e@(BitLiteral _)  = "_ = " ++ show e ++ " :: " ++ check e
reflect (Binder name val) = name ++ " = " ++ (show val) ++ " :: " ++ (check val)
reflect (Bag exprs)       = "_ :: { " ++ (intercalate "; " (nub (map checkFields exprs))) ++ " }"

checkFields e@(BitLiteral _)    = check e
checkFields e@(Binder name val) = name ++ " :: " ++ (check val)
checkFields e@(Bag _)           = check e

check :: Expr -> String
check (BitLiteral bits) = "["++ (show .length $ bits) ++"]"
check (Binder name val) = check val
check (Bag exprs)       = "{ " ++ ((intercalate "; ") . nub . (map checkFields) $ exprs) ++ " }"







-- IGNORE

toCubitType :: Expr -> String
toCubitType (BitLiteral bits)  
            | length bits == 1 = "1bit"
            | otherwise        = (show . length $ bits)++"bits"
toCubitType (Binder atom expr) = toCubitType expr
toCubitType (Bag exprs)        = 
  "{ "++((intercalate "; ") . nub $ (map toCubitType exprs))++" }"

toCryptolType :: Expr -> String
toCryptolType (BitLiteral bits)
              | length bits == 1 = "Bit"
              | otherwise        = "["++(show . length $ bits)++"]"
toCryptolType (Binder atom expr) = toCryptolType expr
toCryptolType (Bag exprs)        = 
  "{ "++((intercalate "; ") . nub $ (map toCryptolType exprs))++" }"