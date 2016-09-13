package com.galois.crucible;

import java.util.*;
import com.galois.crucible.cfg.Position;
import com.galois.crucible.proto.Protos;

/**
   This path aborted message is returned when a simulated branch of execution
   reads from a word map at a location not initalized.
*/
public class ReadBeforeWriteMessage extends SimulatorMessage {
    public ReadBeforeWriteMessage( String message, List<Protos.Position> proto_backtrace ) {
	super(message, proto_backtrace);
    }
    public ReadBeforeWriteMessage( String message ) {
	super(message);
    }
}
