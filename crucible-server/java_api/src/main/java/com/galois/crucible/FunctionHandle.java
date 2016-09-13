package com.galois.crucible;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;

import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/**
 * Represents handles to functions.
 */
public final class FunctionHandle implements SimulatorValue, Expr {
    private final long handleId;
    private final String displayName;
    private final Type[] argTypes;
    private final Type returnType;

    /**
     * Internal method for creating a new handle, see @Simulator.newHandle@
     * for the public interface.  This does the work of talking to the C code
     * to get a new unique ID for the simulator.
     */
    FunctionHandle(long handleId,
                   String displayName,
                   Type[] argTypes,
                   Type returnType) {

        this.handleId = handleId;
        this.displayName = displayName;
        this.argTypes = argTypes.clone();
        this.returnType = returnType;
    }

    /**
     * Create a handle from a handle info.
     */
    FunctionHandle(long handleId, Protos.HandleInfo h) {
        this(handleId,
             h.getDisplayName(),
             Type.typeArrayFromProtoList(h.getArgTypeList()),
             new Type(h.getReturnType()));
    }

    public long getUniqueId() {
        return handleId;
    }

    public String getDisplayName() {
        return displayName;
    }

    public int getArgCount() {
        return argTypes.length;
    }

    /**
     * Return type at given index.
     */
    public Type getArgType(int i) {
        assert 0 <= i && i < argTypes.length;
        return argTypes[i];
    }

    public Type getReturnType() {
        return returnType;
    }

    public Type type() {
        return Type.functionHandle(argTypes, returnType);
    }

    /** Generate protocol repersentation. */
    public Protos.Expr getExprRep() {
        return
            Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.FnHandleExpr)
            .setIndex(handleId)
            .build();
    }

    /** Generate protocol repersentation. */
    public Protos.Value getValueRep() {
        return
            Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.FnHandleValue)
            .setIndex(handleId)
            .build();
    }
}
