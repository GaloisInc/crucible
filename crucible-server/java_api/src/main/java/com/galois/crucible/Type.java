package com.galois.crucible;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.galois.crucible.proto.Protos;

/**
 * Crucible expression types
 */
public final class Type {
    final Protos.CrucibleTypeId id;
    final long width;
    final Type[] params;

    /**
     * Returns whether simulator supports creating constants with this type.
     */
    boolean supportSymbolicConstants() {
        return id == Protos.CrucibleTypeId.BoolType
            || id == Protos.CrucibleTypeId.NatType
            || id == Protos.CrucibleTypeId.BitvectorType;
    }

    /**
     * Create an array of types from a list of protocol buffer types.
     */
    static
    Type[] typeArrayFromProtoList(List<Protos.CrucibleType> l) {
        Type[] r = new Type[l.size()];
        int cnt=0;
        for (Protos.CrucibleType tp : l) {
            r[cnt++] = new Type(tp);
        }
        return r;
    }


    /** A package internal method for creating types from a stream. */
    Type(Protos.CrucibleType type) {
        this.id = type.getId();
        this.width = type.getWidth();
        this.params = typeArrayFromProtoList(type.getParamList());
    }

    /** A private method for creating a type with the given args. */
    private Type(Protos.CrucibleTypeId id, long width, Type[] params) {
        this.id = id;
        this.width = width;
        this.params = params;
    }

    private Type(Protos.CrucibleTypeId id, Type ... args) {
        this.id = id;
        this.width = 0;
        this.params = args;
    }

    public String toString() {
        return getTypeRep().toString();
    }

    /**
     * The type of unit, which contains a single value.
     */
    public static final Type UNIT = new Type(Protos.CrucibleTypeId.UnitType);

    /**
     * Type for Boolean values (true or false)
     */
    public static final Type BOOL = new Type(Protos.CrucibleTypeId.BoolType);

    /**
     * Type for natural numbers.
     */
    public static final Type NAT = new Type(Protos.CrucibleTypeId.NatType);

    /**
     * Type for positive natural numbers.
     */
    public static final Type POS_NAT = new Type(Protos.CrucibleTypeId.PosNatType);

    /**
     * Type for integers
     */
    public static final Type INTEGER = new Type(Protos.CrucibleTypeId.IntegerType);

    /**
     * Type for real numbers
     */
    public static final Type REAL = new Type(Protos.CrucibleTypeId.RealType);

    /**
     * Type for complex real values.
     */
    public static final Type COMPLEX = new Type(Protos.CrucibleTypeId.ComplexType);

    // Cache used for bitvector types.
    private static Map<Long,Type> bitvectorTypes = new HashMap<Long,Type>();

    /**
     * Return a parameter for this type.
     *
     * @param i Index of parameter.
     * @return the parameter
     */
    public Type typeParam(int i) {
        if (!(0 <= i && i < params.length)) {
            throw new IllegalArgumentException("Invalid type parameter.");
        }

        return params[i];
    }

    /**
     * Returns the type of a bitvector with <code>width</code> bits.
     *
     * @param width The number of bits in bitvector.
     * @return The given type.
     */
    public static Type bitvector(long width) {
        synchronized (bitvectorTypes) {
            Type r = bitvectorTypes.get(width);
            if (r == null) {
                r = new Type(Protos.CrucibleTypeId.BitvectorType, width, new Type[0]);
                bitvectorTypes.put(width, r);
            }
            return r;
        }
    }

    /**
     * Returns the type of a word map, which maps <code>width</code> bit wide addresses and
     * to values of type <code>range</code>.
     */
    public static Type wordMap(long width, Type range) {
        return new Type( Protos.CrucibleTypeId.WordMapType, width, new Type[] { range } );
    }


    /**
     * Check if this type is a WordMap.
     * @return true if this type is WordMap
     */
    public boolean isWordMap() {
	return id == Protos.CrucibleTypeId.WordMapType;
    }

    /**
     * Return the range type of a wordmap type.
     * @return The range type of this wordmap type.
     */
    public Type wordMapRangeType() {
        if( id != Protos.CrucibleTypeId.WordMapType ) {
            throw new UnsupportedOperationException("Expected wordmap type");
        }

        if( params.length < 1 || params[0] == null ) {
            throw new UnsupportedOperationException("Ill-formed wordmap type; no parameter type");
        }

        return params[0];
    }

    /**
     * Check if this type is a Struct type
     * @return true if this is a Struct type
     */
    public boolean isStruct() {
        return id == Protos.CrucibleTypeId.StructType;
    }

    /**
     * Check if this type is Vector(t) for some t.
     * @return true if this is a vector type
     */
    public boolean isVector() {
        return id == Protos.CrucibleTypeId.VectorType;
    }

    /**
     * Return the element type of a vector type.
     * @return The element type of this vector type.
     */
    public Type vectorElementType() {
        if( id != Protos.CrucibleTypeId.VectorType ) {
            throw new UnsupportedOperationException("Expected vector type");
        }

        if( params.length < 1 || params[0] == null ) {
            throw new UnsupportedOperationException("Ill-formed vector type; no parameter type");
        }

        return params[0];
    }


    /**
     * Check if  this is a bitvector type.
     * @return Whether this is a bitvector type.
     */
    public boolean isBitvector() {
        return id == Protos.CrucibleTypeId.BitvectorType;
    }

    /**
     * Return width of this type if it is a bitvector, and <code>0</code> otherwise.
     * @return The width
     */
    public long width() {
        return width;
    }

    /**
     * Type for 16-bit IEEE754 floats.
     */
    public static final Type HALF_FLOAT = new Type(Protos.CrucibleTypeId.HalfFloatType);

    /**
     * Type for 32-bit IEEE754 floats.
     */
    public static final Type SINGLE_FLOAT = new Type(Protos.CrucibleTypeId.SingleFloatType);

    /**
     * Type for 64-bit IEEE754 floats.
     */
    public static final Type DOUBLE_FLOAT = new Type(Protos.CrucibleTypeId.DoubleFloatType);

    /**
     * Type for 128-bit IEEE754 floats.
     */
    public static final Type QUAD_FLOAT = new Type(Protos.CrucibleTypeId.QuadFloatType);

    /**
     * Type for 80-bit x87 extended double floating pount.
     */
    public static final Type x86_80_FLOAT = new Type(Protos.CrucibleTypeId.X86_80FloatType);

    /**
     * Type for pair of 64-bit floats that are summed together.
     */
    public static final Type DOUBLE_DOUBLE_FLOAT =
        new Type(Protos.CrucibleTypeId.DoubleDoubleFloatType);

    /**
     * Type for single Unicode character.
     */
    public static final Type CHAR = new Type(Protos.CrucibleTypeId.CharType);

    /**
     * Type for strings of Unicode characters.
     */
    public static final Type STRING = new Type(Protos.CrucibleTypeId.StringType);

    // Cache used for function handle types.
    private static Map<List<Type>,Type> functionHandleTypes =
        new HashMap<List<Type>,Type>();

    /**
     * Type for function handle with given type.
     *
     * @param args Types of function arguments.
     * @param ret Return type of fucntion
     * @return Return type
     */
    public static final Type functionHandle(Type[] args, Type ret) {
        synchronized (functionHandleTypes) {
            ArrayList<Type> params = new ArrayList<Type>();
            params.addAll(Arrays.asList(args));
            params.add(ret);
            Type r = functionHandleTypes.get(params);
            // If we haven't seen this function handle then replace it.
            if (r == null) {
                Type[] params_array = params.toArray(new Type[0]);
                r = new Type(Protos.CrucibleTypeId.FunctionHandleType, 0, params_array);
                functionHandleTypes.put(params, r);
            }
            return r;
        }
    }

    /**
     * Return whether this is a function handle.
     * @return whether this is a handle
     */
    public boolean isFunctionHandle() {
        return id == Protos.CrucibleTypeId.FunctionHandleType;
    }

    /**
     * Return the number of arguments expected by function if this
     * is a function handle.
     * @return the number of arguments.
     */
    public int getFunctionArgumentCount() {
        assert isFunctionHandle();
        return params.length - 1;
    }

    /**
     * Return the type of a function at a given 0-based index.
     * @param i index of argument
     * @return the type
     */
    public Type getFunctionArgumentType(int i) {
        assert isFunctionHandle();
        if (i < 0 || i >= params.length - 1) {
            throw new IllegalArgumentException("Function argument is out of bounds.");
        }
        return params[i];
    }

    /**
     * Return function return type.
     * @return the return type
     */
    public Type getFunctionReturnType() {
        assert isFunctionHandle();
        return params[params.length - 1];
    }

    /** Cache for maybeType */
    private static Map<Type, Type> maybeTypes = new HashMap<Type, Type>();

    /**
     * Returns type that may contain an element of type <code>e</code>.
     *
     * @param e The type of that may be contained.
     * @return The maybe type.
     */
    public static Type maybe(Type e) {
        synchronized (maybeTypes) {
            Type r = maybeTypes.get(e);
            if (r == null) {
                r = new Type(Protos.CrucibleTypeId.MaybeType, e);
                maybeTypes.put(e, r);
            }
            return r;
        }
    }

    public boolean isMaybe() {
        return id == Protos.CrucibleTypeId.MaybeType;
    }

    private static Map<Type, Type> vectorTypes = new HashMap<Type, Type>();

    /**
     * A vector whose elements are of type <code>e</code>.
     *
     * @param e The type of the elements of the vector.
     * @return The vector type.
     */
    public static Type vector(Type e) {
        synchronized (vectorTypes) {
            Type r = vectorTypes.get(e);
            if (r == null) {
                r = new Type(Protos.CrucibleTypeId.VectorType, e);
                vectorTypes.put(e, r);
            }
            return r;
        }
    }

    private static Map<List<Type>, Type> structTypes =
           new HashMap<List<Type>, Type>();

    /**
     * Type for a struct with elements of the given types.
     *
     * @param fields The types of fields in the struct.
     * @return The resulting type.
     */
    public static Type struct(Type[] fields) {
        synchronized (structTypes) {
            List<Type> fieldsList = Arrays.asList(fields);

            Type r = structTypes.get(fieldsList);
            if (r == null) {
                r = new Type(Protos.CrucibleTypeId.StructType, 0, fields);
                structTypes.put(fieldsList, r);
            }
            return r;
        }
    }

    /**
     * Return protocol buffer representation for type.
     * @return the representation
     */
    public Protos.CrucibleType getTypeRep() {
        Protos.CrucibleType.Builder b
            = Protos.CrucibleType.newBuilder()
            .setId(id)
            .setWidth(width);
        for (Type param : params) {
            b.addParam(param.getTypeRep());
        }
        return b.build();
    }

    /**
     * Returns true if <code>this</code> and <code>o</code> are the same type.
     * @param o the other type.
     * @return whether the types are the same.
     */
    public boolean equals(Object o) {
        if (!(o instanceof Type)) return false;
        Type other = (Type) o;
        return this.id.equals(other.id)
            && this.width == other.width
            && Arrays.equals(this.params, other.params);
    }

    public int hashCode() {
        return Arrays.hashCode(new Object[] { id, width, params });
    }
}
