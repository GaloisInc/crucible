/*
Module           : PublicKey.java
Description      :
Stability        : provisional
Point-of-contact : jhendrix

Copyright 2012 Galois, Inc.  All rights reserved.
*/

package com.galois.ecc;

/**
 * An elliptic curve public key created by an <code>ECCProvider</code>.
 * @see ECCProvider
 */
public final class PublicKey {
  PublicKey(int size) {
    this.x = new int[size];
    this.y = new int[size];
  }

  final int[] x;
  final int[] y;
}
