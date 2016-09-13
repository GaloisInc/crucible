package com.galois.crucible.cfg;

import com.galois.crucible.proto.Protos;

public class InternalPosition extends Position {

    public InternalPosition( String functionName )
    {
        this.functionName = functionName;
    }

    public Protos.Position getPosRep()
    {
        Protos.Position.Builder b =
            Protos.Position.newBuilder();

        b.setCode( Protos.PositionCode.InternalPos );
        b.setFunctionName( functionName );
        return b.build();
    }

    public String toString()
    {
        return "internal position: " + functionName;
    }
}
