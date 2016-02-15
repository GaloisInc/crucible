/*
Module           : NISTCurveFactory.java
Description      : This file defines the 32-bit and 64-bit versions of the
                   P384 curves.
Stability        : provisional
Point-of-contact : jhendrix

Copyright 2012 Galois, Inc.  All rights reserved.
*/

package com.galois.ecc;

// NIST32 subclass {{{1

/**
 * Defines arithmetic routines for ECC over prime fields using only 32-bit
 * operations and types, so that it can be run on the SCORE processor.
 */
abstract class NIST32 extends ECCProvider {
  public int field_red_aux(int[] z, int[] a) {
    System.out.println("field_red_aux not implemented for NIST32");
    return 0;
  }

  /**
   * Intermediate buffer used for field multiplication and squaring.
   */
  private int[] a;

  /** Intermediate value used in Karatsuba multiplication. */
  private int[] r;

  protected int[] neg_group_order;

  NIST32(int width,
         int[] field_prime,
         int[] field_unit,
         int[] group_order,
         int[] neg_group_order,
         AffinePoint basePoint) {
    super(width, field_prime, field_unit, group_order, basePoint);
    this.neg_group_order = neg_group_order;
    a = new int[width << 1];
    r = new int[width];
  }

  protected void cleanup() {
    set_zero(a);
    super.cleanup();
  }

  // Bitvector operations {{{3
  static final int INT_MASK = 0xFFFF;

  protected int add(int[] z, int[] x, int[] y) {
    int w = z.length;
    int c = 0;
    for (int i = 0; i != w; ++i) {
      c += (x[i] & INT_MASK) + (y[i] & INT_MASK);
      int v = (c >> 16) + (x[i] >>> 16) + (y[i] >>> 16);
      z[i] = c & INT_MASK | v << 16;
      c = v >> 16;
    }
    return c;
  }

  /**
   * Assigns z = 2 * x and returns carry bit.
   */
  protected int dbl(int[] z, int[] x) {
    final int w = z.length;
    int c = 0;
    for (int i = 0; i != w; ++i) {
      c += (x[i] & INT_MASK) << 1;
      int v = (c >> 16) + ((x[i] >>> 16) << 1);
      z[i] = c & INT_MASK | v << 16;
      c = v >> 16;
    }
    return c;
  }

  /**
   * Assigns z = z - 2 * y and returns carry value (which will be negative or zero).
   */
  protected int dbl_dec(int[] z, int[] x) {
    int w = z.length;
    int c = 0;
    for (int i = 0; i != w; ++i) {
      c += (z[i] & INT_MASK) - ((x[i] & INT_MASK) << 1);
      int v = (c >> 16) + (z[i] >>> 16) - ((x[i] >>> 16) << 1);
      z[i] = c & INT_MASK | v << 16;
      c = v >> 16;
    }
    return c;
  }

  /**
   * Assigns z[zi .. zi+w) = x[xi .. xi+w) + y[yi .. yi+w) and returns carry.
   */
  private int iadd(int[] z, int zi, int[] x, int xi, int[] y, int yi, int w) {
    int c = 0;
    for (int i = w; i != 0; --i) {
      c += (x[xi] & INT_MASK) + (y[yi] & INT_MASK);
      int v = (c >> 16) + (x[xi] >>> 16) + (y[yi] >>> 16);
      z[zi] = c & INT_MASK | v << 16;
      c = v >> 16;
      ++xi;
      ++yi;
      ++zi;
    }
    return c;
  }

  /**
   * Decrements z[zi .. zi+w] by x[zi .. xi+w] and returns carry.
   */
  private int idec(int[] z, int zi, int[] x, int xi, int xw) {
    int c = 0;
    for (int i = xw; i != 0; --i) {
      c += (z[zi] & INT_MASK) - (x[xi] & INT_MASK);
      int v = (c >> 16) + (z[zi] >>> 16) - (x[xi] >>> 16);
      z[zi] = c & INT_MASK | v << 16;
      c = v >> 16;
      ++zi;
      ++xi;
    }
    return c;
  }

  /**
   * Increments z[zi .. zi+w] by x[zi .. xi+w] and returns carry.
   */
  private int iinc(int[] z, int zi, int[] x, int xi, int w) {
    int c = 0;
    for (int i = w; i != 0; --i) {
      c += (z[zi] & INT_MASK) + (x[xi] & INT_MASK);
      int v = (c >> 16) + (z[zi] >>> 16) + (x[xi] >>> 16);
      z[zi] = c & INT_MASK | v << 16;
      c = v >> 16;
      ++zi;
      ++xi;
    }
    return c;
  }

  /**
   * Increments z[zi .. zi+zw] by c and returns carry.
   */
  private int iincc(int[] z, int zi, int zw, int c) {
    for (int i = zw; i != 0 && c != 0; --i) {
      c += z[zi] & INT_MASK;
      int v = (c >> 16) + (z[zi] >>> 16);
      z[zi] = c & INT_MASK | v << 16;
      c = v >> 16;
      ++zi;
    }
    return c;
  }

  /**
   * Assigns a[ai .. ai+2*w] <- x[xi .. xi+w] * y[yi .. yi+w] using schoolbook multiplication.
   */
  private void imul(int[] a, int ai, int[] x, int xi, int[] y, int yi, int w) {
    final int aw = ai + w;
    final int yw = yi + w;
    for (int j = ai; j != aw; ++j) a[j] = 0;

    // Compute multiplication sum in a.
    for (int i = 0; i != w; ++i) {
      int xil = x[xi] & INT_MASK;
      int xih = x[xi] >>> 16;
      ++xi;
      int ij = ai;
      ++ai;

      int c = 0;
      for (int j = yi; j != yw; ++j, ++ij) {
        int yjl = y[j] & INT_MASK;
        int yjh = y[j] >>> 16;

        int mll = xil * yjl;
        int mlh = xil * yjh;
        int mhl = xih * yjl;
        int mhh = xih * yjh;

        int vl = (a[ij] & INT_MASK) + (c & INT_MASK) + mll;
        int vh = (a[ij] >>> 16) + (vl >>> 16) + (c >>> 16) + (mlh & INT_MASK) + (mhl & INT_MASK);
        a[ij] = vl & INT_MASK | vh << 16;
        c = (vh >>> 16) + (mlh >>> 16) + (mhl >>> 16) + mhh;
      }
      // Add final overflow bit.
      a[ij] = c;
    }
  }

  /**
   * Performs one round of Karatsuba multiplication before calling imul.
   */
  private void kmul(int[] a, int[] x, int[] y) {
    int w = x.length;
    int l = w >> 1;

    // [r_0 ..r_l) = x0 + x1
    int c0 = iadd(r, 0, x, 0, x, l, l);
    // [r_l ..r_w) = y0 + y1
    int c1 = iadd(r, l, y, 0, y, l, l);

    // Initialize a[0 .. l)
    for (int i = 0; i != l; ++i) a[i] = 0;
    // Initialize a[l .. l + w)
    imul(a, l, r, 0, r, l, l);
    // Initialize a[w +l .. 2w)
    for (int i = w + l; i != (w << 1); ++i) a[i] = 0;

    if (c1 != 0) a[w + l] += iinc(a, w, r, 0, l);
    if (c0 != 0) a[w + l] += iinc(a, w, r, l, l);
    if ((c0 & c1) != 0) a[w + l] += 1;

    imul(r, 0, x, 0, y, 0, l);
    int c = iinc(a, 0, r, 0, w);
    a[w + l] += iincc(a, w, l, c);
    a[w + l] += idec(a, l, r, 0, w);

    imul(r, 0, x, l, y, l, l);
    a[w + l] += idec(a, l, r, 0, w);
    iinc(a, w, r, 0, w);
  }

  /**
   * Assigns <code>a = x * x</code>
   *
   * @param a Array with <code>2 * x.length</code> elements.
   * @param x Nonempty array with the multiplier.
   */
  protected void sq(int[] a, int[] x) {
    int c;
    int w = x.length;

    for (int j = 0; j != w; ++j) a[j] = 0;

    // Add entries outside of diagonal.
    for (int i = 0; i != w - 1; ++i) {
      int xil = x[i] & INT_MASK;
      int xih = x[i] >>> 16;

      c = 0;

      int ij = (i << 1) + 1;
      for (int j = i + 1; j != w; ++j, ++ij) {
        int xjl = x[j] & INT_MASK;
        int xjh = x[j] >>> 16;

        int mll = xil * xjl;
        int mlh = xil * xjh;
        int mhl = xih * xjl;
        int mhh = xih * xjh;

        int vl = (a[ij] & INT_MASK) + (c & INT_MASK) + mll;
        int vh = (a[ij] >>> 16) + (vl >>> 16) + (c >>> 16) + (mlh & INT_MASK) + (mhl & INT_MASK);
        a[ij] = vl & INT_MASK | vh << 16;
        c = (vh >>> 16) + (mlh >>> 16) + (mhl >>> 16) + mhh;
      }
      a[ij] = c;
    }
    a[23] = 0;

    // Double current entries and add diagonal.
    c = 0;
    for (int i = 0; i != w; ++i) {
      int xil = x[i] & INT_MASK;
      int xih = x[i] >>> 16;

      int mll = xil * xil;
      int mlh = xil * xih;
      int mhh = xih * xih;

      int ij = i << 1;

      int vl = ((a[ij] & INT_MASK) << 1) + (c & INT_MASK) + (mll & INT_MASK);
      int vh = ((a[ij] >>> 16) + (mlh & INT_MASK) << 1) + (vl >>> 16) + (c >>> 16) + (mll >>> 16);
      a[ij] = vl & INT_MASK | vh << 16;
      ++ij;

      vl = ((a[ij] & INT_MASK) + (mlh >>> 16) << 1) + (vh >>> 16) + (mhh & INT_MASK);
      vh = ((a[ij] >>> 16) << 1) + (vl >>> 16) + (mhh >>> 16);
      a[ij] = vl & INT_MASK | vh << 16;
      c = vh >>> 16;
      ++ij;
    }
  }

  /**
   * Assigns z = x - y, and returns ammount borrowed (-1 or 0).
   */
  protected int sub(int[] z, int[] x, int[] y) {
    int c = 0;
    for (int i = 0; i < z.length; ++i) {
      int vl = c + (x[i] & INT_MASK) - (y[i] & INT_MASK);
      int vh = (vl >> 16) + (x[i] >>> 16) - (y[i] >>> 16);
      z[i] = vl & INT_MASK | vh << 16;
      c = vh >> 16;
    }
    return c;
  }

  // Underlying field operations {{{3

  protected void field_mul(int[] z, int[] x, int[] y) {
    imul(a, 0, x, 0, y, 0, x.length);
    field_red(z, a);
  }

  protected void field_sq(int[] z, int[] x) {
    sq(a, x);
    field_red(z, a);
  }

  // Group Field operations {{{3

  /**
   * Reduces bit vector (r + x * (2 ** 384)) modulo group_order
   */
  private void group_red(int[] r, int x) {
    int xl = x & INT_MASK;
    int xh = x >>> 16;
    int c = 0;
    for (int j = 0; j != r.length; ++j) {
      int gjl = neg_group_order[j] & INT_MASK;
      int gjh = neg_group_order[j] >>> 16;

      int mll = xl * gjl;
      int mlh = xl * gjh;
      int mhl = xh * gjl;
      int mhh = xh * gjh;

      int vl = (r[j] & INT_MASK) + (c & INT_MASK) + mll;
      int vh = (r[j] >>> 16) + (vl >>> 16) + (c >>> 16) + (mlh & INT_MASK) + (mhl & INT_MASK);
      r[j] = vl & INT_MASK | vh << 16;
      c = (vh >>> 16) + (mlh >>> 16) + (mhl >>> 16) + mhh;
    }
    while (c != 0) c -= sub(r, r, group_order);
  }

  /**
   *  Assigns r = x * y (mod group_order)
   */
  protected void group_mul(int[] r, int[] x, int[] y) {
    int w = x.length;

    set_zero(r);
    for (int i = w - 1; i != -1; --i) {
      int xil = x[i] & INT_MASK;
      int xih = x[i] >>> 16;

      //System.out.print("r1: "); print(r);
      int rmax = r[w - 1];
      for (int j = w - 1; j != 0; --j) {
        r[j] = r[j-1];
      }
      r[0] = 0;
      group_red(r, rmax);

      int c = 0;
      for (int j = 0; j != w; ++j) {
        int yjl = y[j] & INT_MASK;
        int yjh = y[j] >>> 16;

        int mll = xil * yjl;
        int mlh = xil * yjh;
        int mhl = xih * yjl;
        int mhh = xih * yjh;

        int vl = (r[j] & INT_MASK) + (c & INT_MASK) + mll;
        int vh = (r[j] >>> 16) + (vl >>> 16) + (c >>> 16) + (mlh & INT_MASK) + (mhl & INT_MASK);
        r[j] = vl & INT_MASK | vh << 16;
        c = (vh >>> 16) + (mlh >>> 16) + (mhl >>> 16) + mhh;
      }
      group_red(r, c);
    }
    if (leq(group_order, r)) add(r, r, neg_group_order);
  }
}

// NIST64 subclass {{{1

/**
 * Defines arithmetic routines for ECC over prime fields using a mix of
 * 32 and 64-bit operations with better performance than the
 * NIST32 algorithms on 64-bit machines.
 */
abstract class NIST64 extends ECCProvider {

  /**
   * Intermediate buffer for storing multiplication results.
   */
  private int[] a;

  NIST64(int width,
         int[] field_prime,
         int[] field_unit,
         int[] group_order,
         AffinePoint basePoint) {
    super(width, field_prime, field_unit, group_order, basePoint);
    a = new int[width << 1];
  }

  protected void cleanup() {
    set_zero(a);
    super.cleanup();
  }

  // Bitvector operations {{{2

  static final long LONG_MASK = 0xFFFFFFFFL;

  protected int add(int[] z, int[] x, int[] y) {
    long c = 0;
    for (int i = 0; i != z.length; ++i) {
      c += (x[i] & LONG_MASK) + (y[i] & LONG_MASK);
      z[i] = (int) c; c = c >> 32;
    }
    return (int) c;
  }

  protected int dbl(int[] z, int[] x) {
    long c = 0;
    for (int i = 0; i != z.length; ++i) {
      c += (x[i] & LONG_MASK) << 1;
      z[i] = (int) c; c = c >> 32;
    }
    return (int) c;
  }

  /**
   * Assigns z = z - 2 * y and returns carry value * (which will be negative or zero).
   */
  protected int dbl_dec(int[] z, int[] y) {
    long b = 0;

    for (int i = 0; i != z.length; ++i) {
      b += (z[i] & LONG_MASK) - ((y[i] & LONG_MASK) << 1);
      z[i] = (int) b; b = b >> 32;
    }
    return (int) b;
  }

  private long mul_inner(boolean azero, int[] a, int ij, int xi, int yj, long d) {
    long m = (((long) xi) & LONG_MASK) * (((long) yj) & LONG_MASK);
    long aij;
    if(azero) {
      aij = 0;
    } else {
      aij = a[ij] & LONG_MASK;
    }
    d = d + m + aij;
    a[ij] = (int) d;
    return d >>> 32;
  }

  /**
   * Computes x * y and stores result before reduction in a.
   *
   * @param a Array with at least <code>2 * x.length</code> elements for storing result.
   * @param x The multiplier (contains at least one element).
   * @param y The multiplicand (contains same number of elements as x).
   */
  // Note: this code is actually faster than the original!
  protected void mul(int[] a, int[] x, int[] y) {
    int l = x.length;

    long d = 0;
    for (int j = 0; j != l; ++j) {
      d = mul_inner(true, a, j, x[0], y[j], d);
    }
    // Add final overflow bit.
    a[l] = (int) d;

    // Compute multiplication sum in a.
    for (int i = 1; i != l; ++i) {
      d = 0;
      int ij = i;
      for (int j = 0; j != l; ++j, ++ij) {
        d = mul_inner(false, a, ij, x[i], y[j], d);
      }
      // Add final overflow bit.
      a[ij] = (int) d;
    }
  }

  private long sq_inner1(int[] a, int ij, long c) {
    c += ((a[ij] & LONG_MASK) << 1);
    a[ij] = (int) c;
    c >>>= 32;
    return c;
  }

  private long sq_inner2(int[] a, int ij, int xati, long c) {
    long xi = xati & LONG_MASK;
    long m = xi * xi;

    c += (m & LONG_MASK) + ((a[ij] & LONG_MASK) << 1);
    a[ij] = (int) c;
    c = (c >>> 32) + (m >>> 32);
    return c;
  }

  private void sq_loop(int[] a, int[] x) {
    int l = x.length;
    for (int i = 1; i != l - 1; ++i) {
      long c = 0;
      int ij = i + i + 1;
      for (int j = i + 1; j != l; ++j, ++ij) {
        c = mul_inner(false, a, ij, x[i], x[j], c);
      }
      a[ij] = (int) c;
    }
  }

  /**
   * Assigns <code>a = x * x</code>
   *
   * @param a Array with <code>2 * x.length</code> elements.
   * @param x Nonempty array with the multiplier.
   */
  protected void sq(int[] a, int[] x) {
    long c;
    int l = x.length;

    // Add entries outside of diagonal.
    c = 0;
    for (int j = 1; j != l; ++j) {
      c = mul_inner(true, a, j, x[0], x[j], c);
    }
    // Add final overflow bit.
    a[l] = (int) c;

    sq_loop(a, x);

    // Double current entries and add diagonal.
    c = mul_inner(true, a, 0, x[0], x[0], 0);

    int ij = 1;
    for (int i = 1; i != l; ++i) {
      c = sq_inner1(a, ij, c);
      ++ij;

      c = sq_inner2(a, ij, x[i], c);
      ++ij;
    }

    a[(l << 1) - 1] = (int) c;
  }

  /**
   * Assigns z = x - y, and returns amount borrowed (-1 or 0).
   */
  protected int sub(int[] z, int[] x, int[] y) {
    long b = 0;
    for (int i = 0; i < z.length; ++i) {
      b += (x[i] & LONG_MASK) - (y[i] & LONG_MASK);
      z[i] = (int) b;
      b = b >> 32;
    }
    return (int) b;
  }

  // Underlying field operations {{{2

  protected void field_mul(int[] z, int[] x, int[] y) {
    mul(a, x, y);
    field_red(z, a);
  }

  protected void field_sq(int[] z, int[] x) {
    sq(a, x);
    field_red(z, a);
  }

  // Underlying group scalar operations {{{3

  private long group_red_aux(int[] r, int aj, int j, long c, long b) {
    long m = c * (aj & LONG_MASK);
    b += (r[j] & LONG_MASK) - (m & LONG_MASK);
    r[j] = (int) b;
    b = (b >> 32) - (m >>> 32);
    return b;
  }

  /**
   * Reduces bit vector (r + c * (2 ** 384)) modulo group_order
   */
  private void group_red(int[] r, long c) {
      long b = 0;
      for (int j = 0; j != r.length; ++j) {
        b = group_red_aux(r, group_order[j], j, c, b);
      }

      c += b;
      if (c != 0) {
        c += sub(r, r, group_order);
      }
      if (c != 0) {
        c += sub(r, r, group_order);
      }
  }

  private long array_shift(int[] r) {
    int l = r.length;
    long c = r[l - 1] & LONG_MASK;
    for (int j = l-1; j != 0; --j) {
      r[j] = r[j-1];
    }
    r[0] = 0;
    return c;
  }

  private long group_mul_aux(int[] r, int yj, int j, int xi, long c) {
    long m = (xi & LONG_MASK) * (yj & LONG_MASK);
    c += (r[j] & LONG_MASK) + (m & LONG_MASK);
    r[j] = (int) c;
    c = (c >>> 32) + (m >>> 32);
    return c;
  }

  /**
   *  Assigns r = x * y (mod group_order)
   */
  protected void group_mul(int[] r, int[] x, int[] y) {
    int l = x.length;

    set_zero(r);
    for (int i = l - 1; i != -1; --i) {
      group_red(r, array_shift(r));

      long c = 0;
      for (int j = 0; j != l; ++j) {
        c = group_mul_aux(r, y[j], j, x[i], c);
      }

      group_red(r, c);
    }
    if (leq(group_order, r)) {
      sub(r, r, group_order);
    }
  }
}

// P384 specific constants {{{1

/**
 * Defines constants for P384 curve used by both 32 and 64-bit implementations.
 */
class P384Constants {
  static int[] field_prime = { -1, 0x0, 0x0, -1, -2, -1, -1, -1, -1, -1, -1, -1 };
  static int[] unit_vector = { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
  static int[] group_order = {
      0xccc52973, 0xecec196a, 0x48b0a77a, 0x581a0db2, 0xf4372ddf, 0xc7634d81, -1, -1, -1, -1, -1, -1 };
  static int[] neg_group_order = {
    0x333ad68d, 0x1313e695, 0xb74f5885, 0xa7e5f24d, 0x0bc8d220, 0x389cb27e, 0, 0, 0, 0, 0, 0 };

  static AffinePoint basePoint = new AffinePoint(
    new int[] {
      0x72760ab7, 0x3a545e38, 0xbf55296c, 0x5502f25d, 0x82542a38, 0x59f741e0,
      0x8ba79b98, 0x6e1d3b62, 0xf320ad74, 0x8eb1c71e, 0xbe8b0537, 0xaa87ca22,
    },
    new int[] {
      0x90ea0e5f, 0x7a431d7c, 0x1d7e819d, 0x0a60b1ce, 0xb5f0b8c0, 0xe9da3113,
      0x289a147c, 0xf8f41dbd, 0x9292dc29, 0x5d9e98bf, 0x96262c6f, 0x3617de4a });
}

// P384ECC32 subclass {{{1
class P384ECC32 extends NIST32 {

  P384ECC32() {
    super(12,
          P384Constants.field_prime,
          P384Constants.unit_vector,
          P384Constants.group_order,
          P384Constants.neg_group_order,
          P384Constants.basePoint);
    init();
  }

  static final int INT_MASK = 0xFFFF;

  protected int decFieldPrime(int[] x) {
    int c;
    int v;

    v = x[0];
    c = (v & INT_MASK) + 1;
    v = (c >> 16) + (v >>> 16);
    x[0] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[1];
    c += (v & INT_MASK) + 0xFFFF;
    v = (c >> 16) + (v >>> 16) + 0xFFFF;
    x[1] = (c & INT_MASK) | (v << 16);
    c = v >> 16;

    v = x[2];
    c += (v & INT_MASK) + 0xFFFF;
    v = (c >> 16) + (v >>> 16) + 0xFFFF;
    x[2] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[3];
    c += (v & INT_MASK);
    v = (c >> 16) + (v >>> 16);
    x[3] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[4];
    c += (v & INT_MASK) + 1;
    v = (c >> 16) + (v >>> 16);
    x[4] = c & INT_MASK | v << 16;
    c = v >> 16;

    for (int i = 5; i != 12; ++i) {
      v = x[i];
      c += (v & INT_MASK);
      v = (c >> 16) + (v >>> 16);
      x[i] = c & INT_MASK | v << 16;
      c = v >> 16;
    }

    return c - 1;
  }

  protected int incFieldPrime(int[] x) {
    int c;
    int v;

    v = x[0];
    c = (v & INT_MASK) - 1;
    v = (c >> 16) + (v >>> 16);
    x[0] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[1];
    c += (v & INT_MASK) - 0xFFFF;
    v = (c >> 16) + (v >>> 16) - 0xFFFF;
    x[1] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[2];
    c += (v & INT_MASK) - 0xFFFF;
    v = (c >> 16) + (v >>> 16) - 0xFFFF;
    x[2] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[3];
    c += (v & INT_MASK);
    v = (c >> 16) + (v >>> 16);
    x[3] = c & INT_MASK | v << 16;
    c = v >> 16;

    v = x[4];
    c += (v & INT_MASK) - 1;
    v = (c >> 16) + (v >>> 16);
    x[4] = c & INT_MASK | v << 16;
    c = v >> 16;

    for (int i = 5; i != 12; ++i) {
      v = x[i];
      c += (v & INT_MASK);
      v = (c >> 16) + (v >>> 16);
      x[i] = c & INT_MASK | v << 16;
      c = v >> 16;
    }

    return c + 1;
  }

  public void field_red(int[] z, int[] a) {
    int a12l = a[12] & INT_MASK; int a12h = a[12] >>> 16;
    int a13l = a[13] & INT_MASK; int a13h = a[13] >>> 16;
    int a14l = a[14] & INT_MASK; int a14h = a[14] >>> 16;
    int a15l = a[15] & INT_MASK; int a15h = a[15] >>> 16;
    int a16l = a[16] & INT_MASK; int a16h = a[16] >>> 16;
    int a17l = a[17] & INT_MASK; int a17h = a[17] >>> 16;
    int a18l = a[18] & INT_MASK; int a18h = a[18] >>> 16;
    int a19l = a[19] & INT_MASK; int a19h = a[19] >>> 16;
    int a20l = a[20] & INT_MASK; int a20h = a[20] >>> 16;
    int a21l = a[21] & INT_MASK; int a21h = a[21] >>> 16;
    int a22l = a[22] & INT_MASK; int a22h = a[22] >>> 16;
    int a23l = a[23] & INT_MASK; int a23h = a[23] >>> 16;

    // s1 =     (zero : [128])    # a21 # a22 # a23 #      (zero : [160])         # z32;
    // s2 = a12 # a13 # a14 # a15 # a16 # a17 # a18 # a19 # a20 # a21 # a22 # a23 # z32;
    // s3 = a21 # a22 # a23 # a12 # a13 # a14 # a15 # a16 # a17 # a18 # a19 # a20 # z32;
    // s4 = z32 # a23 # z32 # a20 # a12 # a13 # a14 # a15 # a16 # a17 # a18 # a19 # z32;
    // s5 =     (zero : [128])    # a20 # a21 # a22 # a23 #    (zero : [128])     # z32;
    // s6 = a20 #    z64    # a21 # a22 # a23 #          (zero : [192])           # z32;
    // d1 = a23 # a12 # a13 # a14 # a15 # a16 # a17 # a18 # a19 # a20 # a21 # a22 # z32;
    // d2 = z32 # a20 # a21 # a22 # a23 #              (zero : [224])             # z32;
    // d3 =  (zero : [96])  # a23 # a23 #              (zero : [224])             # z32;

    int c  =  (a[ 0] & INT_MASK)                  + a12l + a21l        + a20l        - a23l;
    int v  = (c >> 16) + (a[ 0] >>> 16)           + a12h + a21h        + a20h        - a23h;
    z[ 0] = c & INT_MASK | v << 16; ; c = v >> 16;

    c += (a[ 1] & INT_MASK)                       + a13l + a22l + a23l               - a12l - a20l;
    v  = (c >> 16) + (a[ 1] >>> 16)               + a13h + a22h + a23h               - a12h - a20h;
    z[ 1] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 2] & INT_MASK)                       + a14l + a23l                      - a13l - a21l;
    v  = (c >> 16) + (a[ 2] >>> 16)               + a14h + a23h                      - a13h - a21h;
    z[ 2] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 3] & INT_MASK)                       + a15l + a12l + a20l + a21l        - a14l - a22l - a23l;
    v  = (c >> 16) + (a[ 3] >>> 16)               + a15h + a12h + a20h + a21h        - a14h - a22h - a23h;
    z[ 3] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 4] & INT_MASK)         + (a21l << 1) + a16l + a13l + a12l + a20l + a22l - a15l - (a23l << 1);
    v  = (c >> 16) + (a[ 4] >>> 16) + (a21h << 1) + a16h + a13h + a12h + a20h + a22h - a15h - (a23h << 1);
    z[ 4] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 5] & INT_MASK)         + (a22l << 1) + a17l + a14l + a13l + a21l + a23l - a16l;
    v  = (c >> 16) + (a[ 5] >>> 16) + (a22h << 1) + a17h + a14h + a13h + a21h + a23h - a16h;
    z[ 5] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 6] & INT_MASK)         + (a23l << 1) + a18l + a15l + a14l + a22l        - a17l;
    v  = (c >> 16) + (a[ 6] >>> 16) + (a23h << 1) + a18h + a15h + a14h + a22h        - a17h;
    z[ 6] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 7] & INT_MASK)                       + a19l + a16l + a15l + a23l        - a18l;
    v  = (c >> 16) + (a[ 7] >>> 16)               + a19h + a16h + a15h + a23h        - a18h;
    z[ 7] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 8] & INT_MASK)                       + a20l + a17l + a16l               - a19l;
    v  = (c >> 16) + (a[ 8] >>> 16)               + a20h + a17h + a16h               - a19h;
    z[ 8] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[ 9] & INT_MASK)                       + a21l + a18l + a17l               - a20l;
    v  = (c >> 16) + (a[ 9] >>> 16)               + a21h + a18h + a17h               - a20h;
    z[ 9] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[10] & INT_MASK)                       + a22l + a19l + a18l               - a21l;
    v  = (c >> 16) + (a[10] >>> 16)               + a22h + a19h + a18h               - a21h;
    z[10] = c & INT_MASK | v << 16; c = v >> 16;

    c += (a[11] & INT_MASK)                       + a23l + a20l + a19l               - a22l;
    v  = (c >> 16) + (a[11] >>> 16)               + a23h + a20h + a19h               - a22h;
    z[11] = c & INT_MASK | v << 16; c = v >> 16;

    if (c > 0) {

      int ofl = c & INT_MASK;
      int ofh = c >>> 16;

      c  = (z[0] & INT_MASK) + ofl;
      v  = (c >> 16) + (z[0] >>> 16) + ofh;
      z[0] = c & INT_MASK | v << 16; c = v >> 16;

      c += (z[1] & INT_MASK) - ofl;
      v  = (c >> 16) + (z[1] >>> 16) - ofh;
      z[1] = c & INT_MASK | v << 16; c = v >> 16;

      c += (z[2] & INT_MASK);
      v  = (c >> 16) + (z[2] >>> 16);
      z[2] = c & INT_MASK | v << 16; c = v >> 16;

      c += (z[3] & INT_MASK) + ofl;
      v  = (c >> 16) + (z[3] >>> 16) + ofh;
      z[3] = c & INT_MASK | v << 16; c = v >> 16;

      c += (z[4] & INT_MASK) + ofl;
      v  = (c >> 16) + (z[4] >>> 16) + ofh;
      z[4] = c & INT_MASK | v << 16; c = v >> 16;

      for (int i = 5; i != 12; ++i) {
        c += z[i] & INT_MASK;
        v  = (c >> 16) + (z[i] >>> 16);
        z[i] = c & INT_MASK | v << 16; c = v >> 16;
      }
    }

    // Perform one addition or subtraction if neccessary.
    while (c > 0) c += decFieldPrime(z);
    while (c < 0) c += incFieldPrime(z);
    if (leq(field_prime, z)) decFieldPrime(z);
  }
}

// P384ECC64 subclass {{{1
class P384ECC64 extends NIST64 {
  P384ECC64() {
    super(12,
          P384Constants.field_prime,
          P384Constants.unit_vector,
          P384Constants.group_order,
          P384Constants.basePoint);
    init();
  }

  protected int decFieldPrime(int[] x) {
    long c = 0;

    c += (x[0] & LONG_MASK) + 0x1L;
    x[0] = (int) c; c = c >> 32;
    c += (x[1] & LONG_MASK) + 0xFFFFFFFFL;
    x[1] = (int) c; c = c >> 32;
    c += (x[2] & LONG_MASK) + 0xFFFFFFFFL;
    x[2] = (int) c; c = c >> 32;
    c += (x[3] & LONG_MASK);
    x[3] = (int) c; c = c >> 32;
    c += (x[4] & LONG_MASK) + 1;
    x[4] = (int) c; c = c >> 32;
    c += (x[5] & LONG_MASK);
    x[5] = (int) c; c = c >> 32;
    c += (x[6] & LONG_MASK);
    x[6] = (int) c; c = c >> 32;
    c += (x[7] & LONG_MASK);
    x[7] = (int) c; c = c >> 32;
    c += (x[8] & LONG_MASK);
    x[8] = (int) c; c = c >> 32;
    c += (x[9] & LONG_MASK);
    x[9] = (int) c; c = c >> 32;
    c += (x[10] & LONG_MASK);
    x[10] = (int) c; c = c >> 32;
    c += (x[11] & LONG_MASK);
    x[11] = (int) c; c = c >> 32;

    return -1 + (int) c;
  }

  protected int incFieldPrime(int[] x) {
    long b = 0;

    b += (x[0] & LONG_MASK) - 0x1L;
    x[0] = (int) b; b = b >> 32;
    b += (x[1] & LONG_MASK) - 0xFFFFFFFFL;
    x[1] = (int) b; b = b >> 32;
    b += (x[2] & LONG_MASK) - 0xFFFFFFFFL;
    x[2] = (int) b; b = b >> 32;
    b += (x[3] & LONG_MASK);
    x[3] = (int) b; b = b >> 32;
    b += (x[4] & LONG_MASK) - 1;
    x[4] = (int) b; b = b >> 32;
    b += (x[5] & LONG_MASK);
    x[5] = (int) b; b = b >> 32;
    b += (x[6] & LONG_MASK);
    x[6] = (int) b; b = b >> 32;
    b += (x[7] & LONG_MASK);
    x[7] = (int) b; b = b >> 32;
    b += (x[8] & LONG_MASK);
    x[8] = (int) b; b = b >> 32;
    b += (x[9] & LONG_MASK);
    x[9] = (int) b; b = b >> 32;
    b += (x[10] & LONG_MASK);
    x[10] = (int) b; b = b >> 32;
    b += (x[11] & LONG_MASK);
    x[11] = (int) b; b = b >> 32;
    return 1 + (int) b;
  }

  public void field_red(int[] z, int[] a) {
    long a0  = a[ 0] & LONG_MASK; long a12 = a[12] & LONG_MASK;
    long a1  = a[ 1] & LONG_MASK; long a13 = a[13] & LONG_MASK;
    long a2  = a[ 2] & LONG_MASK; long a14 = a[14] & LONG_MASK;
    long a3  = a[ 3] & LONG_MASK; long a15 = a[15] & LONG_MASK;
    long a4  = a[ 4] & LONG_MASK; long a16 = a[16] & LONG_MASK;
    long a5  = a[ 5] & LONG_MASK; long a17 = a[17] & LONG_MASK;
    long a6  = a[ 6] & LONG_MASK; long a18 = a[18] & LONG_MASK;
    long a7  = a[ 7] & LONG_MASK; long a19 = a[19] & LONG_MASK;
    long a8  = a[ 8] & LONG_MASK; long a20 = a[20] & LONG_MASK;
    long a9  = a[ 9] & LONG_MASK; long a21 = a[21] & LONG_MASK;
    long a10 = a[10] & LONG_MASK; long a22 = a[22] & LONG_MASK;
    long a11 = a[11] & LONG_MASK; long a23 = a[23] & LONG_MASK;
    long d;

    d =     a0 + a12 + a21 + a20 - a23;                                       z[ 0] = (int) d; d >>= 32;
    d = d + a1 + a13 + a22 + a23 - a12 - a20;                                 z[ 1] = (int) d; d >>= 32;
    d = d + a2 + a14 + a23 - a13 - a21;                                       z[ 2] = (int) d; d >>= 32;
    d = d + a3 + a15 + a12 + a20 + a21 - a14 - a22 - a23;                     z[ 3] = (int) d; d >>= 32;
    d = d + a4 + (a21 << 1) + a16 + a13 + a12 + a20 + a22 - a15 - (a23 << 1); z[ 4] = (int) d; d >>= 32;
    d = d + a5 + (a22 << 1) + a17 + a14 + a13 + a21 + a23 - a16;              z[ 5] = (int) d; d >>= 32;
    d = d + a6 + (a23 << 1) + a18 + a15 + a14 + a22       - a17;              z[ 6] = (int) d; d >>= 32;
    d = d + a7 + a19 + a16 + a15 + a23 - a18;                                 z[ 7] = (int) d; d >>= 32;
    d = d + a8 + a20 + a17 + a16 - a19;                                       z[ 8] = (int) d; d >>= 32;
    d = d + a9 + a21 + a18 + a17 - a20;                                       z[ 9] = (int) d; d >>= 32;
    d = d + a10 + a22 + a19 + a18 - a21;                                      z[10] = (int) d; d >>= 32;
    d = d + a11 + a23 + a20 + a19 - a22;                                      z[11] = (int) d; d >>= 32;

    d = (int) d;

    if (d < 0) {
      incFieldPrime(z);
      return;
    }
    // Subtract prime_field if necessary.
    if (d > 0) {
      long of = d;
      d =     (z[ 0] & LONG_MASK) + of; z[ 0] = (int) d; d >>= 32;
      d = d + (z[ 1] & LONG_MASK) - of; z[ 1] = (int) d; d >>= 32;
      d = d + (z[ 2] & LONG_MASK)     ; z[ 2] = (int) d; d >>= 32;
      d = d + (z[ 3] & LONG_MASK) + of; z[ 3] = (int) d; d >>= 32;
      d = d + (z[ 4] & LONG_MASK) + of; z[ 4] = (int) d; d >>= 32;
      d = d + (z[ 5] & LONG_MASK)     ; z[ 5] = (int) d; d >>= 32;
      d = d + (z[ 6] & LONG_MASK)     ; z[ 6] = (int) d; d >>= 32;
      d = d + (z[ 7] & LONG_MASK)     ; z[ 7] = (int) d; d >>= 32;
      d = d + (z[ 8] & LONG_MASK)     ; z[ 8] = (int) d; d >>= 32;
      d = d + (z[ 9] & LONG_MASK)     ; z[ 9] = (int) d; d >>= 32;
      d = d + (z[10] & LONG_MASK)     ; z[10] = (int) d; d >>= 32;
      d = d + (z[11] & LONG_MASK)     ; z[11] = (int) d; d >>= 32;
    }
    // Perform final subtraction if neccary.
    if (d > 0 || leq(field_prime, z)) decFieldPrime(z);
  }

  public int field_red_aux(int[] z, int[] a) {
    long a0  = a[ 0] & LONG_MASK; long a12 = a[12] & LONG_MASK;
    long a1  = a[ 1] & LONG_MASK; long a13 = a[13] & LONG_MASK;
    long a2  = a[ 2] & LONG_MASK; long a14 = a[14] & LONG_MASK;
    long a3  = a[ 3] & LONG_MASK; long a15 = a[15] & LONG_MASK;
    long a4  = a[ 4] & LONG_MASK; long a16 = a[16] & LONG_MASK;
    long a5  = a[ 5] & LONG_MASK; long a17 = a[17] & LONG_MASK;
    long a6  = a[ 6] & LONG_MASK; long a18 = a[18] & LONG_MASK;
    long a7  = a[ 7] & LONG_MASK; long a19 = a[19] & LONG_MASK;
    long a8  = a[ 8] & LONG_MASK; long a20 = a[20] & LONG_MASK;
    long a9  = a[ 9] & LONG_MASK; long a21 = a[21] & LONG_MASK;
    long a10 = a[10] & LONG_MASK; long a22 = a[22] & LONG_MASK;
    long a11 = a[11] & LONG_MASK; long a23 = a[23] & LONG_MASK;
    long d;

    d =     a0 + a12 + a21 + a20 - a23;                                       z[ 0] = (int) d; d >>= 32;
    d = d + a1 + a13 + a22 + a23 - a12 - a20;                                 z[ 1] = (int) d; d >>= 32;
    d = d + a2 + a14 + a23 - a13 - a21;                                       z[ 2] = (int) d; d >>= 32;
    d = d + a3 + a15 + a12 + a20 + a21 - a14 - a22 - a23;                     z[ 3] = (int) d; d >>= 32;
    d = d + a4 + (a21 << 1) + a16 + a13 + a12 + a20 + a22 - a15 - (a23 << 1); z[ 4] = (int) d; d >>= 32;
    d = d + a5 + (a22 << 1) + a17 + a14 + a13 + a21 + a23 - a16;              z[ 5] = (int) d; d >>= 32;
    d = d + a6 + (a23 << 1) + a18 + a15 + a14 + a22       - a17;              z[ 6] = (int) d; d >>= 32;
    d = d + a7 + a19 + a16 + a15 + a23 - a18;                                 z[ 7] = (int) d; d >>= 32;
    d = d + a8 + a20 + a17 + a16 - a19;                                       z[ 8] = (int) d; d >>= 32;
    d = d + a9 + a21 + a18 + a17 - a20;                                       z[ 9] = (int) d; d >>= 32;
    d = d + a10 + a22 + a19 + a18 - a21;                                      z[10] = (int) d; d >>= 32;
    d = d + a11 + a23 + a20 + a19 - a22;                                      z[11] = (int) d; d >>= 32;

    return (int) d;

    // long d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11;
    // long zd0  =  a0 + a12 + a21 + a20 - a23;                                            z[ 0] = (int) zd0;  d0  = zd0 >> 32;
    // long zd1  =  d0 + a1 + a13 + a22 + a23 - a12 - a20;                                 z[ 1] = (int) zd1;  d1  = zd1 >> 32;
    // long zd2  =  d1 + a2 + a14 + a23 - a13 - a21;                                       z[ 2] = (int) zd2;  d2  = zd2 >> 32;
    // long zd3  =  d2 + a3 + a15 + a12 + a20 + a21 - a14 - a22 - a23;                     z[ 3] = (int) zd3;  d3  = zd3 >> 32;
    // long zd4  =  d3 + a4 + (a21 << 1) + a16 + a13 + a12 + a20 + a22 - a15 - (a23 << 1); z[ 4] = (int) zd4;  d4  = zd4 >> 32;
    // long zd5  =  d4 + a5 + (a22 << 1) + a17 + a14 + a13 + a21 + a23 - a16;              z[ 5] = (int) zd5;  d5  = zd5 >> 32;
    // long zd6  =  d5 + a6 + (a23 << 1) + a18 + a15 + a14 + a22       - a17;              z[ 6] = (int) zd6;  d6  = zd6 >> 32;
    // long zd7  =  d6 + a7 + a19 + a16 + a15 + a23 - a18;                                 z[ 7] = (int) zd7;  d7  = zd7 >> 32;
    // long zd8  =  d7 + a8 + a20 + a17 + a16 - a19;                                       z[ 8] = (int) zd8;  d8  = zd8 >> 32;
    // long zd9  =  d8 + a9 + a21 + a18 + a17 - a20;                                       z[ 9] = (int) zd9;  d9  = zd9 >> 32;
    // long zd10 =  d9 + a10 + a22 + a19 + a18 - a21;                                      z[10] = (int) zd10; d10 = zd10 >> 32;
    // long zd11 = d10 + a11 + a23 + a20 + a19 - a22;                                      z[11] = (int) zd11; d11 = zd11 >> 32;
    // return (int) d11;
  }
}

// NISTCurveFactory {{{1

/**
 * Provides static methods for constructing <code>ECCProviders</code>
 * for some of the NIST curves.
 */
public final class NISTCurveFactory {

  /**
   * Hide constructor so that object cannot be created.
   */
  private NISTCurveFactory() {}

  /**
   * Construct a new provider for the P384 curve that only uses
   * 32bit operations.
   */
  public static ECCProvider createP384_32() {
    return new P384ECC32();
  }

  /**
   * Construct a new provider for the P384 curve that may use
   * 64bit operations.
   */
  public static ECCProvider createP384_64() {
    return new P384ECC64();
  }
}
