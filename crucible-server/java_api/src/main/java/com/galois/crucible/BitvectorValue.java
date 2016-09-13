package com.galois.crucible;

import java.math.BigInteger;
import com.google.protobuf.ByteString;

import com.galois.crucible.proto.Protos;
import com.galois.crucible.cfg.Expr;

/** This represents an integer literal. */
public final class BitvectorValue implements Expr, SimulatorValue {
    private final long width;
    private final BigInteger v;

    public BitvectorValue(long width, BigInteger v) {
        if (v == null) throw new NullPointerException("v");
        this.width = width;
        this.v = v;
    }

    public Type type() {
        return Type.bitvector(width);
    }

    public BigInteger getValue() {
	return v;
    }

    public Protos.Expr getExprRep() {
        return
            Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.BitvectorExpr)
            .setWidth(width)
            .setData(ByteString.copyFrom(v.toByteArray()))
            .build();
    }

    public Protos.Value getValueRep() {
        return
            Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.BitvectorValue)
            .setWidth(width)
            .setData(ByteString.copyFrom(v.toByteArray()))
            .build();
    }

    public String toString() {
        return "0x" + v.toString(16) + ":[" + String.valueOf(width) + "]";
    }

    public boolean equals(Object o) {
        if (!(o instanceof BitvectorValue)) return false;
        BitvectorValue r = (BitvectorValue) o;
        return (width == r.width) && v.equals(r.v);
    }

    public int hashCode() {
        return ((int) width) ^ v.hashCode();
    }

}
