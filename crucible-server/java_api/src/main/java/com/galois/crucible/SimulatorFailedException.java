package com.galois.crucible;

import java.util.*;

/**
 * SimulatorFailedException is an exception called when the simulator fails
 * to execute simulated something.
 */
public class SimulatorFailedException extends RuntimeException {
    SimulatorFailedException(String message) {
        super(message);
    }

    SimulatorFailedException(Throwable cause) {
        super(cause);
    }

}
