package com.galois.crucible;
import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/** A Boolean literal as a simulator value. */
public final class BoolValue implements Expr, SimulatorValue {
    boolean bool;

    public static BoolValue TRUE = new BoolValue(true);
    public static BoolValue FALSE = new BoolValue(false);


    /** Create a new value. */
    private BoolValue(boolean bool) {
        this.bool = bool;
    }

    /**
     * Return the type associated with this value.
     * @return the type of the Boolean value.
     */
    public Type type() {
        return Type.BOOL;
    }

    /**
     * Return the representation of a crucible expression.
     */
    public Protos.Expr getExprRep() {
        return
            Protos.Expr.newBuilder()
            .setCode(bool ? Protos.ExprCode.TrueExpr : Protos.ExprCode.FalseExpr)
            .build();
    }

    /**
     * Return the protocol buffer representation of this value.
     *
     * @return the protocol buffer representation.
     */
    public Protos.Value getValueRep() {
        return
            Protos.Value.newBuilder()
            .setCode(bool ? Protos.ValueCode.TrueValue : Protos.ValueCode.FalseValue)
            .build();
    }

    /**
     * Return Boolean value.
     *
     * @return the value
     */
    public boolean getValue() {
        return bool;
    }

    /**
     * Return string "True" or "False" based on value.
     *
     * @return string representation.
     */
    public String toString() {
        return bool ? "True" : "False";
    }

    public boolean equals(Object o) {
        if (!(o instanceof BoolValue)) return false;
        return bool == ((BoolValue) o).bool;
    }
}
