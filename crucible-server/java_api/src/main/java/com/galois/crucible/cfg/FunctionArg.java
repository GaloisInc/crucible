package com.galois.crucible.cfg;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.Type;

/**
 * An argument to the function.
 */
class FunctionArg implements Expr {
    /** The index of the function argument. */
    final long index;
    /** The type of the function. */
    final Type type;

    FunctionArg(long index, Type type) {
        if (type == null) throw new NullPointerException("type");
        this.index = index;
        this.type  = type;
    }

    public Type type() {
        return this.type;
    }

    public Protos.Expr getExprRep() {
        return Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.FunctionArgExpr)
            .setIndex(index)
            .build();
    }
}
