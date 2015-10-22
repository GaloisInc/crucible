{- |
Module           : $Header$
Description      : Pretty printer for Java Class datatype.
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}

module SAWScript.JavaPretty where

import Data.Maybe (fromMaybe)

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.JVM.Common

import Verifier.Java.Codebase

prettyClass :: Class -> Doc
prettyClass cls = vcat $
  [ empty
  , text "Class name:" <+> text (className cls) <+>
    parens (commas attrs)
  , text "Superclass:" <+> text (fromMaybe "none" (superClass cls))
  , empty
  ] ++
  (if null (classInterfaces cls)
      then []
      else [ text "Interfaces:"
           , indent 2 (vcat (map text (classInterfaces cls)))
           , empty
           ]) ++
  [ text "Fields:"
  , indent 2 (vcat (map prettyField (classFields cls)))
  , empty
  , text "Methods:"
  , indent 2 (vcat (map prettyMethod (classMethods cls)))
  , empty
  ]
  where attrs = concat
          [ if classIsPublic cls then [text "public"] else []
          , if classIsFinal cls then [text "final"] else []
          , if classHasSuperAttribute cls then [text "super"] else []
          , if classIsInterface cls then [text "interface"] else []
          , if classIsAbstract cls then [text "abstract"] else []
          ]

prettyField :: Field -> Doc
prettyField f = hsep $
  [ text (show (fieldVisibility f)) ] ++
  attrs ++
  [ text (show (ppType (fieldType f))) -- TODO: Ick. Different PPs.
  , text (fieldName f)
  ]
  where attrs = concat
          [ if fieldIsStatic f then [text "static"] else []
          , if fieldIsFinal f then [text "final"] else []
          , if fieldIsVolatile f then [text "volatile"] else []
          , if fieldIsTransient f then [text "transient"] else []
          ]

prettyMethod :: Method -> Doc
prettyMethod m =
  hsep [ maybe (text "void") prettyType ret
       , text name
       , (parens . commas . map prettyType) params
       ]
  where (MethodKey name params ret) = methodKey m
        prettyType = text . show . ppType -- TODO: Ick.

commas :: [Doc] -> Doc
commas = sep . punctuate comma
