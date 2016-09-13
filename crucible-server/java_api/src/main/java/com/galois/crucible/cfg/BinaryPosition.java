package com.galois.crucible.cfg;

import com.galois.crucible.proto.Protos;

public class BinaryPosition extends Position {
    String path;
    long addr;

    public BinaryPosition( String functionName, String path, long addr )
    {
        this.functionName = functionName;
        this.path = path;
        this.addr = addr;
    }

    public Protos.Position getPosRep()
    {
        return Protos.Position.newBuilder()
            .setCode( Protos.PositionCode.BinaryPos )
            .setFunctionName( functionName )
            .setPath( path )
            .setAddr( addr )
            .build();
    }

    public String toString()
    {
        return path + ": 0x" + Long.toHexString( addr ) + " " + functionName;
    }

}
