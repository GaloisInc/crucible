# Generated from ./sexpression.g4 by ANTLR 4.10.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .sexpressionParser import sexpressionParser
else:
    from sexpressionParser import sexpressionParser

# This class defines a complete listener for a parse tree produced by sexpressionParser.
class sexpressionListener(ParseTreeListener):

    # Enter a parse tree produced by sexpressionParser#sexpr.
    def enterSexpr(self, ctx:sexpressionParser.SexprContext):
        pass

    # Exit a parse tree produced by sexpressionParser#sexpr.
    def exitSexpr(self, ctx:sexpressionParser.SexprContext):
        pass


    # Enter a parse tree produced by sexpressionParser#comment.
    def enterComment(self, ctx:sexpressionParser.CommentContext):
        pass

    # Exit a parse tree produced by sexpressionParser#comment.
    def exitComment(self, ctx:sexpressionParser.CommentContext):
        pass


    # Enter a parse tree produced by sexpressionParser#item.
    def enterItem(self, ctx:sexpressionParser.ItemContext):
        pass

    # Exit a parse tree produced by sexpressionParser#item.
    def exitItem(self, ctx:sexpressionParser.ItemContext):
        pass


    # Enter a parse tree produced by sexpressionParser#list_.
    def enterList_(self, ctx:sexpressionParser.List_Context):
        pass

    # Exit a parse tree produced by sexpressionParser#list_.
    def exitList_(self, ctx:sexpressionParser.List_Context):
        pass


    # Enter a parse tree produced by sexpressionParser#atom.
    def enterAtom(self, ctx:sexpressionParser.AtomContext):
        pass

    # Exit a parse tree produced by sexpressionParser#atom.
    def exitAtom(self, ctx:sexpressionParser.AtomContext):
        pass



del sexpressionParser