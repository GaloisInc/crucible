/*
Module           : AffinePoint.java
Description      :
Stability        : provisional
Point-of-contact : jhendrix

Copyright 2012 Galois, Inc.  All rights reserved.
*/
package com.galois.ecc;

/**
 * Internally used Jacobian representation of a curve point.
 */
class JacobianPoint {
  JacobianPoint(int size) {
    x = new int[size];
    y = new int[size];
    z = new int[size];
  }

  int[] x;
  int[] y;
  int[] z;

  void clear() {
    ECCProvider.set_zero(x);
    ECCProvider.set_zero(y);
    ECCProvider.set_zero(z);
  }
}
