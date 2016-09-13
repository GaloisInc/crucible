package com.galois.crucible;
import com.galois.crucible.proto.Protos;

/**
 * A simulator value that is stored in the server.
 */
public final class ReferenceValue implements SimulatorValue {
    private final Type type;
    private final long idx;

    ReferenceValue(Type type, long idx) {
        if (type == null) throw new NullPointerException("type");
        this.type = type;
        this.idx  = idx;
    }

    public Type type() {
        return type;
    }

    public Protos.Value getValueRep() {
        return Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.ReferenceValue)
            .setIndex(idx)
            .build();
    }

    public String toString() {
        return "??";
    }

    public boolean equals(Object o) {
        if (!(o instanceof ReferenceValue)) return false;
        return idx == ((ReferenceValue) o).idx;
    }

    public int hashCode() {
        return (int)(idx^(idx>>>32));
    }
}
