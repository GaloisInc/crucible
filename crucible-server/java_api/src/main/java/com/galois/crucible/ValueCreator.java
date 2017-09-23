package com.galois.crucible;
import java.math.BigInteger;
import java.io.IOException;

import com.galois.crucible.proto.Protos;

/**
 * Provides methods for applying primitive operations to values with
 * type <code>T</code>.
 *
 * It requires subclasses to implement <code>applyPrimitive</code>,
 * and then they can automatically inherit a large set of operations.
 */
public abstract class ValueCreator<T extends Typed> {
    /**
     * Apply the primitive operation to the given arguments.
     * @param res Type of result
     */
    protected
    abstract
    T applyPrimitive(Type res, Protos.PrimitiveOp op, Object... args);

    public abstract T bvLiteral( long width, BigInteger val );
    public abstract T natLiteral( BigInteger val );
    public abstract T boolLiteral( boolean val );

    public abstract T callHandle( FunctionHandle hdl, Object... args );

    public T natLiteral( long val )
    {
        return natLiteral( BigInteger.valueOf(val) );
    }

    public T bvLiteral( long width, long val )
    {
        return bvLiteral( width, BigInteger.valueOf(val) );
    }

    /** Complement Boolean value. */
    public T not(T x) {
        if (!x.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("not expects a Boolean argument.");
        return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.BoolNot, x);
    }

    /** And two Boolean values. */
    public T and(T x, T y) {
        if (!x.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("and expects Boolean arguments.");
        if (!y.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("and expects Boolean arguments.");
        return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.BoolAnd, x, y);
    }

    /** Inclusive-or of two Boolean values. */
    public T or(T x, T y) {
        if (!x.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("or expects Boolean arguments.");
        if (!y.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("or expects Boolean arguments.");
        return not(and(not(x), not(y)));
    }

    /** Exclusive-or of two Boolean values. */
    public T xor(T x, T y) {
        if (!x.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("xor expects Boolean arguments.");
        if (!y.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("xor expects Boolean arguments.");
        return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.BoolXor, x, y);
    }

    /**
     * if-then-else applied to values with the same type.
     * We currently support Booleans, natural numbers, integers, real
     * numbers, and bitvectors.
     */
    public T ite(T c, T x, T y) {
        if (!c.type().equals(Type.BOOL))
            throw new UnsupportedOperationException("ite expects Boolean condition.");
        Type type = x.type();
        if (!type.equals(y.type()))
            throw new UnsupportedOperationException("ite expects cases to have same type.");

        Protos.PrimitiveOp op;
        if (type.equals(Type.BOOL)) {
            op = Protos.PrimitiveOp.BoolIte;
        } else if (type.equals(Type.REAL)) {
            op = Protos.PrimitiveOp.RealIte;
        } else if (type.isBitvector()) {
            op = Protos.PrimitiveOp.BVIte;
        } else {
            throw new UnsupportedOperationException("Unsupported type given to ite.");
        }

        return applyPrimitive(type, op, c, x, y);
    }

    /** Convert argument to a real. */
    public T convertToReal(T x) {
        Type x_type = x.type();
        if (x_type.equals(Type.REAL)) {
            return x;
        } else if (x_type.equals(Type.INTEGER)) {
            return applyPrimitive(Type.REAL, Protos.PrimitiveOp.IntegerToReal, x);
        } else if (x_type.equals(Type.NAT)) {
            x = applyPrimitive(Type.INTEGER, Protos.PrimitiveOp.NatToInteger, x);
            return applyPrimitive(Type.REAL, Protos.PrimitiveOp.IntegerToReal, x);
        } else {
            throw new UnsupportedOperationException("convertToReal given unsupported type.");
        }
    }

    /** Convert argument to an integer. */
    public T convertToInteger(T x) {
        Type x_type = x.type();
        if (x_type.equals(Type.INTEGER)) {
            return x;
        } else if (x_type.equals(Type.NAT)) {
            return applyPrimitive(Type.INTEGER, Protos.PrimitiveOp.NatToInteger, x);
        } else {
            throw new UnsupportedOperationException("convertToReal given unsupported type.");
        }
    }

    /** Return true if type is Nat integer or Real */
    private static boolean isNatIntegerOrReal(Type type) {
        return type.equals(Type.NAT)
            || type.equals(Type.INTEGER)
            || type.equals(Type.REAL);
    }

    /**
     * Add two values.
     *
     * This procedure performs some implicit coercisions as follows:
     * * If both arguments are natural numbers, integers, and real numbers, then the
     *   results may be added subject to the following conversions:
     *   1. If either argument is a real or integer, then the values are converted
     *      to reals as needed, and the result is a real.
     *   2. Otherwise, both arguments must be natural numbers, and the result is a
     *      Nat.
     * * If both arguments are bitvectors with the same size, then the numbers are
     *   added.  Overflow bits are discarded.
     * If neither of these conditions are satisfied, then add throws an
     * <code>UnsupportedOperationException</code>.
     */
    public T add(T x, T y) {
        Type x_type = x.type();
        Type y_type = y.type();

        if (isNatIntegerOrReal(x_type)) {
            if (!isNatIntegerOrReal(y_type)) {
                throw new UnsupportedOperationException("add given incompatible types.");
            }
            if (x_type.equals(Type.REAL) || y_type.equals(Type.REAL)) {
                x = convertToReal(x);
                y = convertToReal(y);
                return applyPrimitive(Type.REAL, Protos.PrimitiveOp.RealAdd, x, y);
            } else if (x_type.equals(Type.INTEGER) || y_type.equals(Type.INTEGER)) {
                x = convertToInteger(x);
                y = convertToInteger(y);
                return applyPrimitive(Type.INTEGER, Protos.PrimitiveOp.IntegerAdd, x, y);
            } else { // Both should be nats
                assert (x_type.equals(Type.NAT));
                assert (y_type.equals(Type.NAT));
                return applyPrimitive(Type.NAT, Protos.PrimitiveOp.NatAdd, x, y);
            }
        } else if (x_type.isBitvector()) {
            if (!y_type.equals(x_type)) {
                throw new UnsupportedOperationException("add given incompatible types.");
            }
            return applyPrimitive(x_type, Protos.PrimitiveOp.BVAdd, x, y);
        } else {
            throw new UnsupportedOperationException("add given unsupported type.");
        }
    }

    /**
     * Subtract one value from another.
     */
    public T sub(T x, T y) {
        Type x_type = x.type();
        Type y_type = y.type();

        if (isNatIntegerOrReal(x_type)) {
            if (!isNatIntegerOrReal(y_type)) {
                throw new UnsupportedOperationException("sub given incompatible types.");
            }
            if (x_type.equals(Type.REAL) || y_type.equals(Type.REAL)) {
                x = convertToReal(x);
                y = convertToReal(y);
                return applyPrimitive(Type.REAL, Protos.PrimitiveOp.RealSub, x, y);
            } else {
                x = convertToInteger(x);
                y = convertToInteger(y);
                return applyPrimitive(Type.INTEGER, Protos.PrimitiveOp.IntegerSub, x, y);
            }
        } else if (x_type.isBitvector()) {
            if (!y_type.equals(x_type)) {
                throw new UnsupportedOperationException("sub given incompatible types.");
            }
            return applyPrimitive(x_type, Protos.PrimitiveOp.BVSub, x, y);
        } else {
            throw new UnsupportedOperationException("sub given unsupported type.");
        }
    }

    /**
     * Check if values are equal.
     * @param x first value
     * @param y second value
     * @return boolean value
     */
    public T eq(T x, T y) {
        Type x_type = x.type();
        Type y_type = x.type();
        if (!x_type.equals(y_type)) {
            throw new UnsupportedOperationException("Values to eq must have same type.");
        }

        if (x_type.equals(Type.BOOL)) {
            return not(xor(x, y));
        } else if (x_type.equals(Type.NAT)) {
            return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.NatEq, x, y);
        } else if (x_type.equals(Type.INTEGER)) {
            return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.IntegerEq, x, y);
        } else if (x_type.equals(Type.REAL)) {
            return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.RealEq, x, y);
        } else if (x_type.isBitvector()) {
            return applyPrimitive(Type.BOOL, Protos.PrimitiveOp.BVEq, x,  y);
        } else {
            throw new UnsupportedOperationException("eq given unsupported type.");
        }
    }

    // ************** Bitvector ops ***************


    /**
     * Apply a binary operation on bitvectors.  The two expressions
     * must both be of the same bitvector type, and the result is of the same type.
     */
    private T bvbinop( Protos.PrimitiveOp op, T x, T y )
    {
        Type x_type = x.type();
        Type y_type = y.type();

        if( !(x_type.isBitvector() && x_type.equals(y_type) ) ) {
            throw new UnsupportedOperationException("binary bitvetor operation given unsupported types" +
                                                    x_type.toString() + " " + y_type.toString() );
        }

        return applyPrimitive( x_type, op, x, y );
    }

    /**
     *  Apply a binary comparison operator to bitvectors.  The two expressions
     *  must both be of the same bitvector type.
     */
    private T bvcmpop( Protos.PrimitiveOp op, T x, T y )
    {
        Type x_type = x.type();
        Type y_type = y.type();

        if( !(x_type.isBitvector() && x_type.equals(y_type) ) ) {
            throw new UnsupportedOperationException("binary bitvector comparison operation given unsupported types" +
                                                    x_type.toString() + " " + y_type.toString() );
        }

        return applyPrimitive( Type.BOOL, op, x, y );
    }

    /**
     *  Apply a _signed_ binary comparison operator to bitvectors.  The two expressions
     *  must both be of the same bitvector type, and must be of nonzero width.
     */
    private T bvscmpop( Protos.PrimitiveOp op, T x, T y )
    {
        Type x_type = x.type();
        Type y_type = y.type();

        if( !(x_type.isBitvector() && x_type.width() > 0 && x_type.equals(y_type) ) ) {
            throw new UnsupportedOperationException("signed binary bitvector comparison operation given unsupported types" +
                                                    x_type.toString() + " " + y_type.toString() );
        }

        return applyPrimitive( Type.BOOL, op, x, y );
    }

    /**
     * Bitvector addition.
     * @param x
     * @param y
     */
    public T bvAdd( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVAdd, x, y );
    }

    /**
     * Bitvector subtraction.
     * @param x
     * @param y
     */
    public T bvSub( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVSub, x, y );
    }

    /**
     * Bitvector multiplication.
     * @param x
     * @param y
     */
    public T bvMul( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVMul, x, y );
    }

    /**
     * Bitvector unsigned division
     * @param x
     * @param y
     */
    public T bvUdiv( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVUdiv, x, y );
    }

    /**
     * Bitvector signed division
     * @param x
     * @param y
     */
    public T bvSdiv( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVSdiv, x, y );
    }

    /**
     * Bitvector unsigned remainder
     * @param x
     * @param y
     */
    public T bvUrem( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVUrem, x, y );
    }

    /**
     * Bitvector signed remainder
     * @param x
     * @param y
     */
    public T bvSrem( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVSrem, x, y );
    }

    /**
     * If-then-else for bitvectors.
     * @param c the boolean value to branch on
     * @param x the "then" value
     * @param y the "else" value
     */
    public T bvIte( T c, T x, T y ) {
        Type c_type = c.type();
        Type x_type = x.type();
        Type y_type = y.type();

        if( !(c_type.equals(Type.BOOL)) ) {
            throw new UnsupportedOperationException("First argument of bvIte is required to be a boolean, but was in fact " +
                                                     c_type.toString() );
        }

        if( !(x_type.isBitvector() && x_type.equals(y_type)) ) {
            throw new UnsupportedOperationException("Invalid types passed to bvIte" +
                                                     x_type.toString() + " " + x_type.toString() );
        }

        return applyPrimitive( x_type, Protos.PrimitiveOp.BVIte, c, x, y );
    }

    /**
     * Compare two bitvectors for equality.
     * @param x First parameter
     * @param y Second parameter
     * @return true iff x is equal to y
     */
    public T bvEq( T x, T y ) {
        return bvcmpop( Protos.PrimitiveOp.BVEq, x, y );
    }

    /**
     * Unsigned less-than-or-equal test.
     * @param x
     * @param y
     * @return true iff x &lt;= y when x and y are interpreted as unsigned values
     */
    public T bvUle( T x, T y ) {
        return bvcmpop( Protos.PrimitiveOp.BVUle, x, y );
    }

    /**
     * Unsigned less-than test.
     * @param x
     * @param y
     * @return true iff x &lt; y when x and y are interpreted as unsigned values
     */
    public T bvUlt( T x, T y ) {
        return bvcmpop( Protos.PrimitiveOp.BVUlt, x, y );
    }

    /**
     * Signed less-than-or-equal test.
     * @param x
     * @param y
     * @return true iff x &lt;= y when x and y are interpreted as 2's complement signed values
     */
    public T bvSle( T x, T y ) {
        return bvscmpop( Protos.PrimitiveOp.BVSle, x, y );
    }

    /**
     * Signed less-than test.
     * @param x
     * @param y
     * @return true iff x &lt; y when x and y are interpreted as 2's complement signed values
     */
    public T bvSlt( T x, T y ) {
        return bvscmpop( Protos.PrimitiveOp.BVSlt, x, y );
    }

    /**
     * Shift left.
     * @param x
     * @param y
     * @return The value x shifted left by y bits.  Zeros are shifted into the least significant bits.
     */
    public T bvShl( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVShl, x, y );
    }

    /**
     * Logical shift right.
     * @param x
     * @param y
     * @return The value x shifted right by y bits.  Zeros are shifted into the most significant bits.
     */
    public T bvLshr( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVLshr, x, y );
    }

    /**
     * Arithmetic shift right.
     * @param x
     * @param y
     * @return The value x shifted right by y bits.  The most significant bit of x is replicated as the value is shifted.
     */
    public T bvAshr( T x, T y ) {
        return bvbinop( Protos.PrimitiveOp.BVAshr, x, y );
    }

    /**
     * Bitwise logical negation.
     * @param x
     * @return bitvector value with every bit flipped from x
     */
    public T bvNot( T x ) {
        Type x_type = x.type();
        if( !(x_type.isBitvector()) ) {
            throw new UnsupportedOperationException("bvNot operation given unsupported type" +
                                                    x_type.toString() );
        }
        return applyPrimitive(x_type, Protos.PrimitiveOp.BVNot, x );
    }

    /**
     * Bitwise logical conjunction.
     * @param x
     * @param y
     */
    public T bvAnd( T x, T y ) {
        return bvbinop(Protos.PrimitiveOp.BVAnd, x, y );
    }

    /**
     * Bitwise logical disjunction.
     * @param x
     * @param y
     */
    public T bvOr( T x, T y ) {
        return bvbinop(Protos.PrimitiveOp.BVOr, x, y );
    }

    /**
     * Bitwise logical exclusive or.
     * @param x
     * @param y
     */
    public T bvXor( T x, T y ) {
        return bvbinop(Protos.PrimitiveOp.BVXor, x, y );
    }

    /**
     * Truncate a bitvector to the given width.  The target width must be
     * no more than the width of x.
     * @param x the value to truncate
     * @param w the target width
     * @return x truncated to w bits
     */
    public T bvTrunc( T x, long w ) {
        Type x_type = x.type();
        if( !(x_type.isBitvector()) ) {
            throw new UnsupportedOperationException("bvTrunc given unsupported type " +
                                                    x_type.toString() );
        }

        if( !(0 <= w && w <= x_type.width()) ) {
            throw new UnsupportedOperationException("invalid trunctaction of type " +
                                                    x_type.toString() + " to length " + w );
        }

        return applyPrimitive( Type.bitvector(w), Protos.PrimitiveOp.BVTrunc, x );
    }

    /**
     * Zero-extend a bitvector to the given width.  The target width must be
     * no less than the width of x.
     * @param x the value to truncate
     * @param w the target width
     * @return x zero-extended to w bits
     */
    public T bvZext( T x, long w ) {
        Type x_type = x.type();
        if( !(x_type.isBitvector()) ) {
            throw new UnsupportedOperationException("bvZext given unsupported type " +
                                                    x_type.toString() );
        }

        if( !(x_type.width() <= w) ) {
            throw new UnsupportedOperationException("invalid zero extension of type " +
                                                    x_type.toString() + " to length " + w );
        }

        return applyPrimitive( Type.bitvector(w), Protos.PrimitiveOp.BVZext, x );
    }

    /**
     * Sign-extend a bitvector to the given width.  The target width must be
     * no less than the width of x (which must be at least 1)
     * @param x the value to truncate
     * @param w the target width
     * @return x zero-extended to w bits
     */
    public T bvSext( T x, long w ) {
        Type x_type = x.type();
        if( !(x_type.isBitvector() && x_type.width() >= 1) ) {
            throw new UnsupportedOperationException("bvSext given unsupported type " +
                                                    x_type.toString() );
        }

        if( !(x_type.width() <= w) ) {
            throw new UnsupportedOperationException("invalid zero extension of type " +
                                                    x_type.toString() + " to length " + w );
        }

        return applyPrimitive( Type.bitvector(w), Protos.PrimitiveOp.BVZext, x );
    }

    /**
     * Select a subsequence from a bitvector.  Take <code>n</code> bits starting at index <code>idx</code>
     * (counting from the least-significant bit as 0) from the bitvector <code>x</code>.  <code>x</code> must
     * be a bitvector with width at least <code>idx + n </code>.
     * @param idx the index to begin selecting bits (least significant bit is 0)
     * @param n the number of bits to take
     * @param x the bitvector from which to select
     * @return the n-bit subsequence of x starting at idx
     */
    public T bvSelect( int idx, int n, T x ) {
        Type x_type = x.type();

        if( !(x_type.isBitvector()) ) {
            throw new UnsupportedOperationException("bvSelect given unsupported type " +
                                                    x_type.toString() );
        }

        if( !(0 <= idx && 0 <= n && idx + n <= x_type.width() ) ) {
            throw new UnsupportedOperationException("bvSelect subsequence out of bounds " +
                                                    idx + " " + n + " " + x_type.toString() );
        }

        return applyPrimitive( Type.bitvector( n ),
                               Protos.PrimitiveOp.BVSelect,
                               natLiteral(idx),
                               natLiteral(n),
                               x );
    }

    /**
     * Concatenate two bitvectors
     * @param x high-order bitvector of width m
     * @param y low-order bitvector of width n
     * @return concatenated bitvector of width (m+n)
     */
    public T bvConcat( T x, T y ) {
        Type x_type = x.type();
        Type y_type = y.type();
        if( !(x_type.isBitvector() && y_type.isBitvector()) ) {
            throw new UnsupportedOperationException("bvConcat given unsupported types " +
                                                    x_type.toString() + " " + y_type.toString() );
        }

        Type ret_type = Type.bitvector( x_type.width() + y_type.width() );

        return applyPrimitive( ret_type, Protos.PrimitiveOp.BVConcat, x, y );
    }

    /**
     * Concatenate a sequence of bitvectors together in bigendian format.  That is,
     * index 0 contains the high order bits and index (N-1) contains the low-order bits.
     * If xs contains 0 elements, the 0-width bitvector is returned.  If xs contains
     * 1 element, it is returned unchanged.
     * @param xs An array of bitvectors to concatenate
     * @return concateneated bitvector
     */
    public T bvConcat( T[] xs ) {
        if( xs.length == 0 ) { return bvLiteral( 0, BigInteger.ZERO ); }

        // Note: this loop structure is designed to produce a right-associated
        // sequence of binary bvConcat operations.  It's not clear that this
        // actually matters...

        int i = xs.length - 1;
        T acc = xs[i];
        while( i > 0 ) {
            i--;
            acc = bvConcat( xs[i], acc );
        }

        return acc;
    }

    public T bvNonzero( T x ) {
        Type x_type = x.type();
        if( !(x_type.isBitvector()) ) {
            throw new UnsupportedOperationException("bvNonzero given unsupported type " +
                                                    x_type.toString() );
        }

        return applyPrimitive( Type.BOOL, Protos.PrimitiveOp.BVNonzero, x );
    }

    public T bvCarry( T x, T y ) {
        return bvcmpop( Protos.PrimitiveOp.BVCarry, x, y );
    }

    public T bvSCarry( T x, T y ) {
        return bvscmpop( Protos.PrimitiveOp.BVSCarry, x, y );
    }

    public T bvSBorrow( T x, T y ) {
        return bvscmpop( Protos.PrimitiveOp.BVSBorrow, x, y );
    }

    public T boolToBV( T x, long width ) {
        Type x_type = x.type();
        if( !x_type.equals( Type.BOOL ) ) {
            throw new UnsupportedOperationException("boolToBV given unsupported type " +
                                                    x_type.toString() );
        }

        if( !(width >= 0) ) {
            throw new UnsupportedOperationException("boolToBV given negative width " + width);
        }

        return applyPrimitive( Type.bitvector(width), Protos.PrimitiveOp.BoolToBV, x );
    }


    // ************** Vector ops ***************
    public T vectorLit( Type type, T... xs ) throws Exception {
        for(int i=0; i<xs.length; i++ ) {
            if( !(type.equals(xs[i].type())) ) {
                throw new UnsupportedOperationException("type mismatch in vectorLit");
            }
        }

        return applyPrimitive( Type.vector(type), Protos.PrimitiveOp.VectorLit, xs );
    }

    public T vectorReplicate( T n, T elem ) throws Exception {
        Type n_type = n.type();
        Type elem_type = elem.type();

        if( !(n_type.equals( Type.NAT )) ) {
            throw new UnsupportedOperationException("expected Nat in vectorReplicate");
        }

        return applyPrimitive( Type.vector(elem_type), Protos.PrimitiveOp.VectorReplicate, n, elem );
    }

    public T vectorSize( T v ) throws Exception {
        Type v_type = v.type();
        if( !(v_type.isVector()) ) {
            throw new UnsupportedOperationException("expected Vector type in vectorSize");
        }

        return applyPrimitive( Type.NAT, Protos.PrimitiveOp.VectorSize, v );
    }

    public T vectorGetEntry( T v, T n ) throws Exception {
        Type v_type = v.type();
        Type n_type = n.type();

        if( !(v_type.isVector()) ) {
            throw new UnsupportedOperationException("expected Vector type in vectorGetEntry");
        }
        if( !(n_type.equals( Type.NAT )) ) {
            throw new UnsupportedOperationException("expected Nat in vectorGetEntry");
        }

        return applyPrimitive( v_type.vectorElementType(), Protos.PrimitiveOp.VectorGetEntry, v, n );
    }

    public T vectorSetEntry( T v, T n, T elem ) throws Exception {
        Type v_type = v.type();
        Type n_type = n.type();
        Type elem_type = elem.type();

        if( !(v_type.isVector()) ) {
            throw new UnsupportedOperationException("expected Vector type in vectorSetEntry");
        }
        if( !(n_type.equals( Type.NAT )) ) {
            throw new UnsupportedOperationException("expected Nat in vectorSetEntry");
        }
        if( !(elem_type.equals( v_type.vectorElementType() ))) {
            throw new UnsupportedOperationException("type mismatch in vectorSetEntry");
        }

        return applyPrimitive( v_type, Protos.PrimitiveOp.VectorSetEntry, v, n, elem );
    }

    // ******************* Struct Ops *****************************************
    public T structLiteral( T... vals ) {
        Type tys[] = new Type[ vals.length ];
        for( int i=0; i<vals.length; i++ ) {
            tys[i] = vals[i].type();
        }
        Type retType = Type.struct( tys );

        return applyPrimitive( retType, Protos.PrimitiveOp.StructLiteral, vals );
    }

    public T structGet( int idx, T struct ) {
        Type s_ty = struct.type();
        if( !(s_ty.isStruct() ) ) {
            throw new UnsupportedOperationException("Expected struct value in structGet, but got" + s_ty.toString());
        }

        Type retType = s_ty.typeParam( idx );

        return applyPrimitive( retType, Protos.PrimitiveOp.StructGet, natLiteral(idx), struct );
    }

    public T structSet( T struct, int idx, T x ) {
        Type s_ty = struct.type();
        Type x_ty = x.type();

        if( !(s_ty.isStruct() ) ) {
            throw new UnsupportedOperationException("Expected struct value in structSet");
        }
        if( !(s_ty.typeParam(idx).equals( x_ty )) ) {
            throw new UnsupportedOperationException("Type mismatch in structSet");
        }

        return applyPrimitive( s_ty, Protos.PrimitiveOp.StructSet, struct, natLiteral(idx), x );
    }

    // ******************* WordMap Ops ****************************************

    public T emptyWordMap( long width, Type range ) {
        if( width < 0 ) {
            throw new UnsupportedOperationException("illegal negative width in emptyWordMap: " + width );
        }

        return applyPrimitive( Type.wordMap( width, range ), Protos.PrimitiveOp.WordMapEmpty );
    }

    public T insertWordMap( T idx, T elem, T map ) {
        Type idx_type = idx.type();
        Type elem_type = elem.type();
        Type map_type = map.type();

        if( !(map_type.isWordMap()
              && idx_type.isBitvector()
              && map_type.wordMapRangeType().equals( elem_type )
              && map_type.width() == idx_type.width()) ) {
            throw new UnsupportedOperationException("illegal types in insertWordMap : "+
                                                    idx_type + " " + elem_type + " " + map_type );
        }

        return applyPrimitive( map_type, Protos.PrimitiveOp.WordMapInsert, idx, elem, map );
    }

    public T lookupWordMap( T idx, T map ) {
        Type idx_type = idx.type();
        Type map_type = map.type();

        if( !(map_type.isWordMap()
              && idx_type.isBitvector()
              && map_type.width() == idx_type.width()) ) {
            throw new UnsupportedOperationException("illegal types in lookupWordMap"+
                                                    idx_type + " " + map_type );
        }

        return applyPrimitive( map_type.wordMapRangeType(), Protos.PrimitiveOp.WordMapLookup, idx, map );
    }

    public T lookupWordMapWithDefault( T idx, T map, T elem ) {
        Type idx_type = idx.type();
        Type map_type = map.type();
        Type elem_type = elem.type();

        if( !(map_type.isWordMap()
              && idx_type.isBitvector()
              && map_type.wordMapRangeType().equals( elem_type )
              && map_type.width() == idx_type.width()) ) {
            throw new UnsupportedOperationException("illegal types in lookupWordMapWithDefault" +
                                                    idx_type + " " + map_type + " " + elem_type );
        }

        return applyPrimitive( elem_type, Protos.PrimitiveOp.WordMapLookupWithDefault, idx, map, elem );
    }

    public T nothingValue( Type elemType ) {
        return applyPrimitive( Type.maybe(elemType), Protos.PrimitiveOp.NothingValue );
    }

    public T justValue( T elem ) {
        return applyPrimitive( Type.maybe(elem.type()), Protos.PrimitiveOp.JustValue, elem );
    }

    public T showValue( T x ) {
        return applyPrimitive( Type.STRING, Protos.PrimitiveOp.ShowValue, x );
    }

    public T isConcrete( T x ) {
	return applyPrimitive( Type.BOOL, Protos.PrimitiveOp.IsConcrete, x );
    }
}
