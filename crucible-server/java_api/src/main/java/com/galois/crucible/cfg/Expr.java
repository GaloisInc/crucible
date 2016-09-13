package com.galois.crucible.cfg;
import java.io.IOException;
import java.io.OutputStream;

import com.galois.crucible.proto.Protos;
import com.galois.crucible.Typed;

/**
 * Interface that all expressions referenced in control flow graph must implement.
 */
public interface Expr extends Typed {
    /**
     * Return the Protocol Buffer representation of an expression.
     * @return the representation
     */
    Protos.Expr getExprRep();
}
