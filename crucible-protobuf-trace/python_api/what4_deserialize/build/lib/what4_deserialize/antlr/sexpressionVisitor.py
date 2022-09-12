# Generated from ./sexpression.g4 by ANTLR 4.10.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .sexpressionParser import sexpressionParser
else:
    from sexpressionParser import sexpressionParser

# This class defines a complete generic visitor for a parse tree produced by sexpressionParser.

class sexpressionVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by sexpressionParser#sexpr.
    def visitSexpr(self, ctx:sexpressionParser.SexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by sexpressionParser#comment.
    def visitComment(self, ctx:sexpressionParser.CommentContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by sexpressionParser#item.
    def visitItem(self, ctx:sexpressionParser.ItemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by sexpressionParser#list_.
    def visitList_(self, ctx:sexpressionParser.List_Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by sexpressionParser#atom.
    def visitAtom(self, ctx:sexpressionParser.AtomContext):
        return self.visitChildren(ctx)



del sexpressionParser