module SAWScript.Token where

data TokenClass
  = Keyword
  | Bitfield
  | String
  | Integer
  | Infix
  | OutfixL
  | OutfixR
  | Postfix
  | Identifier
  | EOF
  deriving (Eq,Show)

data Token p = Token
  { tokClass :: TokenClass
  , tokPos   :: p
  , tokStr   :: String
  } deriving (Eq,Show)

