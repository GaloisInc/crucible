package com.galois.crucible;
import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/** This represents the unit value. */
public final class UnitValue implements Expr, SimulatorValue {
    public UnitValue() {}

    public Type type() {
        return Type.UNIT;
    }

    public Protos.Expr getExprRep() {
        return Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.UnitExpr)
            .build();
    }

    public Protos.Value getValueRep() {
        return Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.UnitValue)
            .build();
    }

    public String toString() {
        return "()";
    }

    public boolean equals(Object o) {
        return (o instanceof UnitValue);
    }

    public int hashCode() {
        return 0;
    }
}
