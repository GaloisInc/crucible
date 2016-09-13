package com.galois.crucible.cfg;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.Type;

/**
 * An argument passed to a Lambda block.
 */
public final class LambdaArg implements Expr {
    private final long block_index;
    private final Type type;

    LambdaArg(long block_index, Type type) {
        this.block_index = block_index;
        this.type = type;
    }

    public Type type() {
        return type;
    }

    public Protos.Expr getExprRep() {
        return Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.LambdaArgExpr)
            .setBlockId(block_index)
            .build();
    }


}
