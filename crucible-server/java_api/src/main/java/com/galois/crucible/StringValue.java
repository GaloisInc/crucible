package com.galois.crucible;
import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/** A constant string in the simulator. */
public final class StringValue implements Expr, SimulatorValue {
    private final String v;

    public StringValue(String v) {
        this.v = v;
    }


    /** Returns string type. */
    public Type type() {
        return Type.STRING;
    }

    public Protos.Expr getExprRep() {
        return Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.StringExpr)
            .setStringLit(v)
            .build();
    }

    public Protos.Value getValueRep() {
        return Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.StringValue)
            .setStringLit(v)
            .build();
    }
}
