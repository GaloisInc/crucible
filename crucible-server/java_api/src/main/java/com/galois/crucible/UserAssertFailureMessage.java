package com.galois.crucible;

import java.util.*;
import com.galois.crucible.cfg.Position;
import com.galois.crucible.proto.Protos;

/**
   This path aborted message is returned when an explicit assertion (i.e., an assert statement
   in a CFG) fails.
*/
public class UserAssertFailureMessage extends SimulatorMessage {
    public UserAssertFailureMessage( String message, List<Protos.Position> proto_backtrace ) {
	super(message, proto_backtrace);
    }
    public UserAssertFailureMessage( String message ) {
	super(message);
    }
}

