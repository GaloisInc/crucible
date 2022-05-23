# next

* The return type of `prog`:

  ```hs
  TopParser s (Map GlobalName (Pair TypeRepr GlobalVar), [ACFG ext])
  ```

  Has been changed to:

  ```hs
  TopParser s (ParsedProgram ext)
  ```

  Where the `parsedProgGlobals :: Map GlobalName (Pair TypeRepr GlobalVar)` and
  `parsedProgCFGs :: [ACFG ext]` fields of `ParsedProgram` now serve the roles
  previously filled by the first and second fields of the returned tuple.

# 0.2

* Various functions now take a `?parserHooks :: ParserHooks ext` implicit
  argument, which supports arbitrary syntax extensions. Various data types now
  also have an additional `ext` type parameter, which represents the type of
  the parser extension being used. If you do not care about parser extensions,
  a reasonable default choice is `?parserHooks = defaultParserHooks`.
