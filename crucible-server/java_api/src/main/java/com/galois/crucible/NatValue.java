package com.galois.crucible;
import java.math.BigInteger;
import com.google.protobuf.ByteString;
import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/** A constant natural number in the simulator. */
public final class NatValue implements SimulatorValue, Expr {
    private final BigInteger v;

    public NatValue(BigInteger i) {
        if (i == null) throw new NullPointerException("i");
        if (i.signum() == -1)
            throw new IllegalArgumentException("Natural numbers cannot be negative.");
        this.v = i;
    }

    public Type type() {
        return Type.NAT;
    }

    private ByteString getDataRep() {
        return ByteString.copyFrom(v.toByteArray());
    }

    public Protos.Expr getExprRep() {
        return
            Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.NatExpr)
            .setData(getDataRep())
            .build();
    }

    public Protos.Value getValueRep() {
        return
            Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.NatValue)
            .setData(getDataRep())
            .build();
    }

    public boolean equals(Object o) {
        if (!(o instanceof NatValue)) return false;
        return v.equals(((NatValue) o).v);
    }

    public int hashCode() {
        return v.hashCode();
    }

    public String toString() {
        return v.toString();
    }
}
