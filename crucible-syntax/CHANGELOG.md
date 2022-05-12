# 0.2

* Various functions now take a `?parserHooks :: ParserHooks ext` implicit
  argument, which supports arbitrary syntax extensions. Various data types now
  also have an additional `ext` type parameter, which represents the type of
  the parser extension being used. If you do not care about parser extensions,
  a reasonable default choice is `?parserHooks = defaultParserHooks`.
