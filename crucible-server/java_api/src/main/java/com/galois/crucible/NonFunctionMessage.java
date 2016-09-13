package com.galois.crucible;

import java.util.*;
import com.galois.crucible.cfg.Position;
import com.galois.crucible.proto.Protos;

/**
   This path aborted message is returned when a SimulatorValue that is not a function
   handle is passed to the runCall() method.
*/
public class NonFunctionMessage extends SimulatorMessage {
    public NonFunctionMessage( String message, List<Protos.Position> proto_backtrace ) {
	super(message, proto_backtrace);
    }
    public NonFunctionMessage( String message ) {
	super(message);
    }
}

