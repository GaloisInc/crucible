
class TreePrintingVisitor(sexpressionVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.indent = 0

    def visitAtom(self, ctx: sexpressionParser.AtomContext):
        print("  " * self.indent + "Atom: " + ctx.getText())
        self.indent += 1
        res = super().visitAtom(ctx)
        self.indent -= 1
        return res

    def visitSexpr(self, ctx: sexpressionParser.SexprContext):
        print("  " * self.indent + "Sexpr: " + ctx.getText())
        self.indent += 1
        res = super().visitSexpr(ctx)
        self.indent -= 1
        return res

    def visitList_(self, ctx: sexpressionParser.List_Context):
        print("  " * self.indent + "List: " + ctx.getText())
        self.indent += 1
        res = super().visitList_(ctx)
        print("RESRESRES", res)
        self.indent -= 1
        return res