package com.galois.crucible;
import com.galois.crucible.proto.Protos;

/**
 * Interface that all values in simulator must implement.
 */
public interface SimulatorValue extends Typed {
    /**
     * Return the Protocol Buffer representation of a simulator value.
     * @return the representation
     */
    Protos.Value getValueRep();
}
