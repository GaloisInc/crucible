package com.galois.crucible;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import com.google.protobuf.ByteString;
import com.galois.crucible.cfg.Expr;
import com.galois.crucible.proto.Protos;

/** A simulator value containing a rational constant. */
public final class RationalValue implements SimulatorValue, Expr {
    private final BigInteger numerator;
    private final BigInteger denominator;

    /**
     * Create a value from an integer.
     * @param n the numerator
     */
    public RationalValue(BigInteger n) {
        if (n == null) throw new NullPointerException("n");
        this.numerator = n;
        this.denominator = BigInteger.valueOf(1);
    }

    /**
     * Create a value from an rational.
     * @param n the numerator
     * @param d the denominator
     */
    public RationalValue(BigInteger n, BigInteger d) {
        if (n == null) throw new NullPointerException("n");
        if (d == null) throw new NullPointerException("d");
        if (d.signum() == 0)
            throw new IllegalArgumentException("d must be non-zero.");
        // Negate numerator and denominator if d is negative.
        if (d.signum() == -1) {
            n = n.negate();
            d = d.negate();
        }

        // Compute gcd to normalize coefficients.
        BigInteger g = n.gcd(d);
        this.numerator = n.divide(g);
        this.denominator = d.divide(g);
    }

    public RationalValue(byte[] bytes) {
        // Create stream.
        ByteArrayInputStream s = new ByteArrayInputStream(bytes);

        // Read unsigned varint for denominator.
        BigInteger d = readUVarint(s);

        // Get remaining bytes.
        byte[] remaining = new byte[s.available()];
        s.read(remaining, 0, s.available());

        BigInteger n = new BigInteger(remaining);

        // Compute gcd.
        BigInteger g = n.gcd(d);
        if (!g.equals(BigInteger.valueOf(1))) {
            throw new IllegalArgumentException(
              "BigInteger(byte[]) expected values in reduced form.");
        }
        this.numerator = n;
        this.denominator = d;
    }

    public Type type() {
        return Type.REAL;
    }

    /** Return numerator of rational. */
    public BigInteger numerator() {
        return numerator;
    }

    /** Return denominator  of rational. */
    public BigInteger denominator() {
        return denominator;
    }

    private static BigInteger readUVarint(ByteArrayInputStream s) {
        BigInteger r = BigInteger.valueOf(0);
        int shift = 0;

        // Read bytes until we reach end.
        while (true) {
            int next = s.read();
            r = r.or(BigInteger.valueOf(next & 0x7f).shiftLeft(shift));
            shift += 7;
            if ((next & 0x80) == 0) break;
        }

        // Return result.
        return r;
    }

    private static void writeUVarint(ByteArrayOutputStream s, BigInteger r) {
        if (r.signum() == -1) {
            throw new IllegalArgumentException("writeUVarint given negative number.");
        }
        // Handle special case of zero to simplify rest of code.
        if (r.signum() == 0) {
            s.write(0);
            return;
        }
        // Get number of bytes needed to store r.
        int cnt = (r.bitLength() + 6) / 7;
        // Write non-terminal bytes.
        while (cnt > 1) {
            --cnt;
            // Get 7 bits at current offset.
            int val = r.shiftRight(7*cnt).intValue() & 0x7f;
            // Write 7 bits with extra bit to denote continuation.
            s.write(val | 0x80);
        }
        // Get 7 bits at current offset.
        s.write(r.intValue() & 0x7f);
    }

    private ByteString getDataRep() {
        ByteArrayOutputStream s = new ByteArrayOutputStream();
        // Write denominator first.
        writeUVarint(s, denominator);
        // Now write numerator.
        byte[] bytes = numerator.toByteArray();
        // We use this function to avoid spurious IOException
        s.write(bytes, 0, bytes.length);
        return ByteString.copyFrom(s.toByteArray());
    }

    public Protos.Expr getExprRep() {
        return Protos.Expr.newBuilder()
            .setCode(Protos.ExprCode.RationalExpr)
            .setData(getDataRep())
            .build();
    }

    public Protos.Value getValueRep() {
        return Protos.Value.newBuilder()
            .setCode(Protos.ValueCode.RationalValue)
            .setData(getDataRep())
            .build();
    }

    /** Check if two rationals are equal. */
    public boolean equals(Object o) {
        if (!(o instanceof RationalValue)) return false;
        RationalValue r = (RationalValue) o;
        // Rationals are stored in reduced form, so equality is quick.
        return numerator.equals(r.numerator)
            && denominator.equals(r.denominator);
    }

    /** Get hashcode for rational. */
    public int hashCode() {
        return numerator.hashCode() ^ denominator.hashCode();
    }

    /** Print rational as a numerator over divisor. */
    public String toString() {
        if (denominator.equals(BigInteger.valueOf(1))) {
            return numerator.toString();
        } else {
            return numerator.toString() + "/" + denominator.toString();
        }
    }
}
