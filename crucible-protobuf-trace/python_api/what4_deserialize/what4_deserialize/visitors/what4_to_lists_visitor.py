import json
from ..antlr.sexpressionVisitor import sexpressionVisitor

class What4ToListsVisitor(sexpressionVisitor):
    def visitSexpr(self, ctx):
        comment = ctx.comment().getText()
        assert comment.startswith(';; ')
        metadata = json.loads(comment[3:])
        exprs = [self.visit(c) for c in ctx.item()]
        return metadata, exprs

    def visitAtom(self, ctx):
        return ctx.getText()

    def visitComment(self, ctx):
        return ctx.getText()

    def visitList_(self, ctx):
        return [self.visit(c) for c in ctx.item()]