{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : lerkok
-}

{-# LANGUAGE DeriveFunctor #-}
module SAWScript.Token where

data Token p = TVar      { tokPos :: p, tokStr :: String                               }
             | TQVar     { tokPos :: p, tokStr :: String, tokVars :: ([String],String) }
             | TLit      { tokPos :: p, tokStr :: String                               }
             | TCode     { tokPos :: p, tokStr :: String                               }
             | TCType    { tokPos :: p, tokStr :: String                               }
             | TUnknown  { tokPos :: p, tokStr :: String                               }
             | TPunct    { tokPos :: p, tokStr :: String                               }
             | TReserved { tokPos :: p, tokStr :: String                               }
             | TOp       { tokPos :: p, tokStr :: String                               }
             | TNum      { tokPos :: p, tokStr :: String, tokNum :: Integer            }
             | TCmntS    { tokPos :: p, tokStr :: String                               }
             | TCmntE    { tokPos :: p, tokStr :: String                               }
             | TEOF      { tokPos :: p, tokStr :: String                               }
             deriving (Show, Functor)
