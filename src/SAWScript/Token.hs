{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : lerkok
-}

{-# LANGUAGE DeriveFunctor #-}
module SAWScript.Token where

data Token p = TVar      { tokPos :: p, tokStr :: String                     }
             | TLit      { tokPos :: p, tokStr :: String                     }
             | TUnknown  { tokPos :: p, tokStr :: String                     }
             | TPunct    { tokPos :: p, tokStr :: String                     }
             | TReserved { tokPos :: p, tokStr :: String                     }
             | TOp       { tokPos :: p, tokStr :: String                     }
             | TNum      { tokPos :: p, tokStr :: String, tokNum :: Integer  }
             | TCmntS    { tokPos :: p, tokStr :: String                     }
             | TCmntE    { tokPos :: p, tokStr :: String                     }
             | TEOF      { tokPos :: p, tokStr :: String                     }
             deriving (Show, Functor)
