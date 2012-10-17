module SAWScript.Token where

data Token p = 
    Keyword     { tokPos :: p, tokStr :: String }
  | InfixOp     { tokPos :: p, tokStr :: String }
  | String      { tokPos :: p, tokStr :: String }
  | OutfixL     { tokPos :: p, tokStr :: String }
  | OutfixR     { tokPos :: p, tokStr :: String }
  | Pattern     { tokPos :: p, tokStr :: String }
  | Identifier  { tokPos :: p, tokStr :: String }
  | ArrowType   { tokPos :: p, tokStr :: String }
  | TEOF        { tokPos :: p, tokStr :: String } deriving Show
    