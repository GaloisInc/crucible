package com.galois.crucible.cfg;

import com.galois.crucible.proto.Protos;

public abstract class Position {
    String functionName;
    String getFunctionName() { return functionName; }

    public abstract Protos.Position getPosRep();

    public static Position fromProto( Protos.Position p ) {
        switch( p.getCode() ) {
        case InternalPos:
            return new InternalPosition( p.getFunctionName() );
        case SourcePos:
            return new SourcePosition( p.getFunctionName(),
                                       p.getPath(),
                                       p.getLine(),
                                       p.getCol() );
        case BinaryPos:
            return new BinaryPosition( p.getFunctionName(),
                                       p.getPath(),
                                       p.getAddr() );
        default:
            throw new Error("Unknown Position code: "+p.getCode());
        }
    }
}
