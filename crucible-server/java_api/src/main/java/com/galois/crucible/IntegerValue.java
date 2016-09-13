package com.galois.crucible;
import java.math.BigInteger;
import com.google.protobuf.ByteString;
import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/**
 * A specific integer simulator value.
 */
public final class IntegerValue implements SimulatorValue, Expr {
    private final BigInteger v;

    public IntegerValue(long i) {
        this.v = BigInteger.valueOf(i);
    }

    public IntegerValue(BigInteger i) {
        if (i == null) throw new NullPointerException("i");
        this.v = i;
    }

    public Type type() {
        return Type.INTEGER;
    }

    private ByteString getDataRep() {
        return ByteString.copyFrom(v.toByteArray());
    }

    public Protos.Expr getExprRep() {
        return
            Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.IntegerExpr)
            .setData(getDataRep())
            .build();
    }

    public Protos.Value getValueRep() {
        return
            Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.IntegerValue)
            .setData(getDataRep())
            .build();
    }

    public boolean equals(Object o) {
        if (!(o instanceof IntegerValue)) return false;
        return v.equals(((IntegerValue) o).v);
    }

    /**
     * Returns hash code of integer.
     */
    public int hashCode() {
        return v.hashCode();
    }

    /**
     * Returns decimal representation of string.
     */
    public String toString() {
        return v.toString();
    }
}
