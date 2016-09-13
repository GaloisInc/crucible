package com.galois.crucible;

import java.util.*;
import com.galois.crucible.cfg.Position;
import com.galois.crucible.proto.Protos;

public class SimulatorMessage {
    String message;
    List<Position> backtrace;

    public SimulatorMessage( String message ) {
        this.message = message;
    }

    protected SimulatorMessage( String message, List<Protos.Position> proto_backtrace ) {
        this.message = message;
        this.backtrace = new LinkedList<Position>();

        for( Protos.Position pp : proto_backtrace ) {
            backtrace.add( Position.fromProto( pp ) );
        }
    }

    public static SimulatorMessage parsePathAbortedMessage( Protos.PathAbortedMessage msg ) {
	String s = msg.getMessage();
	List<Protos.Position> bt = msg.getBacktraceList();

	switch( msg.getCode() ) {
	case AbortedReadBeforeWrite:
	    return new ReadBeforeWriteMessage( s, bt );
	case AbortedNonFunction:
	    return new NonFunctionMessage( s, bt );
        case AbortedUserAssertFailure:
	    return new UserAssertFailureMessage( s, bt );
	default:
	    return new SimulatorMessage( s, bt );
	}
    }


    public String getMessage()
    {
        return message;
    }

    public List<Position> getBacktrace()
    {
        if( backtrace == null ) {
            backtrace = new LinkedList<Position>();
        }

        return backtrace;
    }

    public String toString()
    {
        StringBuilder b = new StringBuilder();
	b.append( this.getClass().getName() );
	b.append( ": ");
        b.append( message );
        if( backtrace != null ) {
            for( Position p : backtrace ) {
                b.append( "\n  at " );
                b.append( p.toString() );
            }
        }

        return b.toString();
    }
}
