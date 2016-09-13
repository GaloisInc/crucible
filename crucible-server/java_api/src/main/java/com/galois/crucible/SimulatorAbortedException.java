package com.galois.crucible;

import java.util.*;

/**
 * SimulatorAbortedException is an exception thrown when calling a simulator
 * function failed along all simulator paths.
 */
public class SimulatorAbortedException extends SimulatorFailedException {
    final List<SimulatorMessage> simMessages;

    SimulatorAbortedException(List<SimulatorMessage> simMessages ) {
        super("Simulation failed along all paths");
	this.simMessages = simMessages;
    }

    public List<SimulatorMessage> getMessages()
    {
        return simMessages;
    }
}
