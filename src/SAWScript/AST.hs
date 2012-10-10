module AST where

data BitField = [Bool]

data Expr =
    BitLiteral BitField
  | Binder String Expr
  | Bag [Expr]

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