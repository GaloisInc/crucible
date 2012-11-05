module SAWScript.Token where

data Token p =
   Keyword    { tokPos :: p, tokStr :: String }
 | Bitfield   { tokPos :: p, tokStr :: String }
 | String     { tokPos :: p, tokStr :: String }
 | Integer    { tokPos :: p, tokStr :: String }
 | Infix      { tokPos :: p, tokStr :: String }
 | OutfixL    { tokPos :: p, tokStr :: String }
 | OutfixR    { tokPos :: p, tokStr :: String }
 | Postfix    { tokPos :: p, tokStr :: String }
 | Identifier { tokPos :: p, tokStr :: String }
 | EOF        { tokPos :: p, tokStr :: String } deriving Show