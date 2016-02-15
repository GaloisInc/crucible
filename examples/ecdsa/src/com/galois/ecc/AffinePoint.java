/*
Module           : AffinePoint.java
Description      : Provides an internal representation of affine points.
Stability        : provisional
Point-of-contact : jhendrix

Copyright 2012 Galois, Inc.  All rights reserved.
*/
package com.galois.ecc;

/**
 * Internallly used affine representation of a curve point.
 */
class AffinePoint {
  AffinePoint(int size) {
    this.x = new int[size];
    this.y = new int[size];
  }

  AffinePoint(int[] x, int[] y) {
    this.x = x;
    this.y = y;
  }

  /** Normalized field x coordinate. */
  int[] x;

  /** Normalized field y coordinate. */
  int[] y;

  void clear() {
    ECCProvider.set_zero(x);
    ECCProvider.set_zero(y);
  }
}
