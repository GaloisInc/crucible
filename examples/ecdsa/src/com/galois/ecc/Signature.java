/*
Module           : Signature.java
Description      :
Stability        : provisional
Point-of-contact : jhendrix

Copyright 2012 Galois, Inc.  All rights reserved.
*/

package com.galois.ecc;

/**
 * An elliptic curve signature created by <code>ECCProvider</code>.
 *
 * @see ECCProvider
 */
public final class Signature {
  Signature(int width) {
    r = new int[width];
    s = new int[width];
  }

  final int[] r;
  final int[] s;
}
