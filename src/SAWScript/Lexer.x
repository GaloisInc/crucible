{
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE BangPatterns #-}
module SAWScript.Lexer
  ( AlexPosn(..)
  , scan
  , lexSAW
  ) where

import SAWScript.Token
import SAWScript.Utils

import Control.Arrow (second)
import Numeric
import Data.List

}


%wrapper "posn"

$whitechar = [\ \t\n\r\f\v]
$special   = [\(\)\,\;\[\]\`\{\}]
$digit     = 0-9
$large     = [A-Z]
$small     = [a-z]
$alpha     = [$small $large]
$symbol    = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~] # [$special \_\:\"\']
$graphic   = [$alpha $symbol $digit $special \:\"\'\_]
$binit     = 0-1
$octit     = 0-7
$hexit     = [0-9 A-F a-f]
$idchar    = [$alpha $digit \' \_]
$codechar  = [$graphic $whitechar]

@reservedid  = import|and|let|fun|in|do|if|then|else|as|undefined
             |prim|CryptolSetup|JavaSetup|LLVMSetup
             |ProofScript|TopLevel
             |Int|String|Term|Bit
             |Simpset|Theorem
             |JavaType|JavaMethodSpec|JavaClass
             |LLVMType|LLVMMethodSpec|LLVMModule
             |Uninterp
             |ProofResult|SatResult

@punct       = "," | ";" | "(" | ")" | ":" | "::" | "[" | "]" | "<-" | "->"
             | "=" | "{" | "}" | "." | "\"
@reservedop  = "~"  | "-" | "*" | "+" | "/" | "%" | ">>" | "<<" | "|" | "&"
             | "^" | "#"  | "==" | "!=" | ">=" | ">" | "<=" |"<" | "&&"
             | "||" | "==>" | "@"
@varid       = $alpha $idchar*
@decimal     = $digit+
@binary      = $binit+
@octal       = $octit+
@hexadecimal = $hexit+
$cntrl       = [$large \@\[\\\]\^\_]
@ascii       = \^ $cntrl | NUL | SOH | STX | ETX | EOT | ENQ | ACK
             | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
             | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
             | SUB | ESC | FS | GS | RS | US | SP | DEL
$charesc     = [abfnrtv\\\"\'\&]
@escape      = \\ ($charesc | @ascii | @decimal | o @octal | x @hexadecimal)
@gap         = \\ $whitechar+ \\
@string      = $graphic # [\"\\] | " " | @escape | @gap
@code        = ($codechar # \}) | \} ($codechar # \})
@num         = @decimal | 0[bB] @binary | 0[oO] @octal | 0[xX] @hexadecimal

sawTokens :-

$white+                          ;
"\n"                             ;
"//".*                           ;
"/*"                             { cnst TCmntS           }
"*/"                             { cnst TCmntE           }
@reservedid                      { TReserved             }
@punct                           { TPunct                }
@reservedop                      { TOp                   }
@varid                           { TVar                  }
\" @string* \"                   { TLit  `via'` read     }
\{\{ @code* \}\}                 { TCode `via'` readCode }
@decimal                         { TNum  `via`  read     }
0[bB] @binary                    { TNum  `via`  readBin  }
0[oO] @octal                     { TNum  `via`  read     }
0[xX] @hexadecimal               { TNum  `via`  read     }
.                                { TUnknown              }

{

cnst f p s   = f p s
via  c g p s = c p s (g s)
via' c g p s = c p (g s)

lexSAW :: FilePath -> String -> [Token Pos]
lexSAW f = dropComments . map (fmap fixPos) . alexScanTokens
  where fixPos (AlexPn _ l c) = Pos f l c

readCode :: String -> String
readCode = reverse . drop 2 . reverse . drop 2

readBin :: String -> Integer
readBin s = case readInt 2 isDigit cvt s' of
              [(a, "")] -> a
              _         -> error $ "Cannot read a binary number from: " ++ show s
  where cvt c = ord c - ord '0'
        isDigit = (`elem` "01")
        s' | "0b" `isPrefixOf` s = drop 2 s
           | "0B" `isPrefixOf` s = drop 2 s
           | True                = s

dropComments :: [Token Pos] -> [Token Pos]
dropComments = go 0
  where go :: Int -> [Token Pos] -> [Token Pos]
        go _  []                 = []
        go !i (TCmntS _ _ : ts)  = go (i+1) ts
        go !i (TCmntE _ _ : ts)
         | i > 0                 = go (i-1) ts
        go !i (t : ts)
         | i /= 0                = go i ts
         | True                  = t : go i ts


alexEOF = (TEOF (error "alexEOF") "")

scan :: Monad m => FilePath -> String -> m [Token Pos]
scan f = return . lexSAW f
}
