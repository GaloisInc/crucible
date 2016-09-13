package com.galois.crucible.cfg;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.Type;

/**
 * An expression obtained by evaluating a statement.
 */
public class StatementResult implements Expr {
    final long blockIndex;
    final long statementIndex;
    final Type type;

    StatementResult(long blockIndex, long statementIndex, Type type) {
        if (type == null) {
            throw new NullPointerException("type is null.");
        }
        this.blockIndex = blockIndex;
        this.statementIndex = statementIndex;
        this.type = type;
    }

    public Type type() {
        return type;
    }

    /**
     * Return the representation of a crucible expression.
     */
    public Protos.Expr getExprRep() {
        return Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.StatementResultExpr)
            .setBlockId(blockIndex)
            .setIndex(statementIndex)
            .build();
    }
}
