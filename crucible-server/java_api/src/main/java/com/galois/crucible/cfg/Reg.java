package com.galois.crucible.cfg;
import java.io.IOException;
import java.io.OutputStream;

import com.galois.crucible.Type;
import com.galois.crucible.Typed;

/**
 * A mutable register that can be modified during execution.
 */
public final class Reg implements Typed {
    private final long index;
    private final Type type;

    /** Package level method for creating a register. */
    Reg(long index, Type type) {
        this.index = index;
        this.type = type;
    }

    /** Get index of register. */
    long index() {
        return index;
    }


    /**
     * Get type of register.
     * @return The type.
     */
    public Type type() {
        return type;
    }
}
