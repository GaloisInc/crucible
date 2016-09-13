package com.galois.crucible;
import com.google.protobuf.CodedOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.List;
import java.util.LinkedList;

import com.galois.crucible.proto.Protos;

/**
 * A type that the simulator allows variables to be created for.
 */
public final class VarType {
    final Protos.VarTypeId id;
    final long width;
    final List<Long> dimensions;

    /** A package internal method for creating types from a stream. */
    VarType(Protos.VarType type) {
        this.id = type.getId();
        this.width = type.getWidth();
	this.dimensions = type.getDimensionList();
    }

    /** A private method for creating a type. */
    private VarType(Protos.VarTypeId id) {
        this.id = id;
        this.width = 0;
	this.dimensions = null;
    }

    /** A private method for creating a type with the given width. */
    private VarType(Protos.VarTypeId id, long width) {
        this.id = id;
        this.width = width;
	this.dimensions = null;
    }

    private VarType(Protos.VarTypeId id, long width, List<Long> dimensions) {
        this.id = id;
        this.width = width;
	this.dimensions = dimensions;
    }

    /**
     * Boolean values (true or false)
     */
    public static final VarType BOOL = new VarType(Protos.VarTypeId.BoolVarType);

    /**
     * Type for integers
     */
    public static final VarType INTEGER = new VarType(Protos.VarTypeId.IntegerVarType);

    /**
     * Type for real numbers
     */
    public static final VarType REAL = new VarType(Protos.VarTypeId.RealVarType);

    /**
     * Returns the type of a bitvector with <code>width</code> bits.
     *
     * @param width The number of bits in bitvector.
     * @return The given type.
     */
    public static VarType bitvector(long width) {
        return new VarType(Protos.VarTypeId.BitvectorVarType, width);
    }

    public static VarType vector( long n, VarType t ) {
	LinkedList<Long> d = null;
	if( t.dimensions == null ) {
	    d = new LinkedList<Long>();
	    d.addFirst( n );
	} else {
	    d = new LinkedList<Long>( t.dimensions );
	    d.addFirst( n );
	}

	return new VarType( t.id, t.width, d );
    }

    /**
     * Get representation of VarType in protocol buffer format.
     */
    Protos.VarType getProtosRep() {
	Protos.VarType.Builder b = Protos.VarType.newBuilder()
            .setId(id)
            .setWidth(width);

	if( dimensions != null ) {
	    b.addAllDimension( dimensions );
	}

	return b.build();
    }

    /** Compare if object equals this. */
    public boolean equals(Object o) {
        if (!(o instanceof VarType)) return false;
        VarType other = (VarType) o;
        return this.id.equals(other.id)
            && this.width == other.width;
    }

    /** Hash fields together. */
    public int hashCode() {
        return Arrays.hashCode( new Object[] { id, width } );
    }
}
