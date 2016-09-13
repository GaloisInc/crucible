package com.galois.crucible.cfg;

import com.galois.crucible.proto.Protos;

public class SourcePosition extends Position {
    String path;
    long line;
    long col;

    public SourcePosition( String functionName, String path, long line, long col )
    {
        this.functionName = functionName;
        this.path = path;
        this.line = line;
        this.col  = col;
    }

    public Protos.Position getPosRep()
    {
        return Protos.Position.newBuilder()
            .setCode( Protos.PositionCode.SourcePos )
            .setFunctionName( functionName )
            .setPath( path )
            .setLine( line )
            .setCol( col )
            .build();
    }

    public String toString()
    {
        return path + ":" + line + ":" + col + " " + functionName;
    }
}
