/*
Module           : ECC.java
Description      :
Stability        : provisional
Point-of-contact : jhendrix

Copyright 2012 Galois, Inc.  All rights reserved.
*/

package com.galois.ecc;
import java.util.Random;

/**
 * Code for testing ECC Implementation.
 */
public final class ECC {

  public static void print(int[] x) {
    System.out.print("0x");
    for(int i = x.length - 1; i != -1; --i) {
      System.out.print(String.format("%8x ", x[i]));
    }

    System.out.println();
  }

  static void randomIntArray(Random r, int[] x) {
    for (int i = 0; i != x.length; ++i) {
      x[i] = r.nextInt(); 
    }
  }

  public static void main(String [] args) {

    // Create ECCProvider over P384 curve with 64bit operations.
    ECCProvider ecc = NISTCurveFactory.createP384_64();
    int[] d = new int[] {
         0x97583480, 0xa61b5fdd, 0x59d2d111, 0x4f76f456, 0xf111a5c4, 0xac052ed1,
         0x61b5a8fd, 0x104311a7, 0x6085a24c, 0x93ab3e62, 0xa6659834, 0xa4ebcae5 };
    int[] e = new int[] {
         0x3e75385d, 0x2afbc689, 0x95301a18, 0xab8cf150, 0x80b38d81, 0xbcfcae21,
         0x0e12ce89, 0x9f4ba9aa, 0x8e1349b2, 0x7acbd600, 0x9a3a76c8, 0xafcf8811 };
    int[] k = new int[] {
         0x1e73cb0e, 0x62b1332d, 0x459da98e, 0xebab4167, 0x68ada415, 0x85dda827,
         0x9cb6f923, 0xae4d89e6, 0xc23997e1, 0xb3be971c, 0x1bbd23f2, 0xfba203b8 };

    Random r = new Random(42);
    
    // Create object for storing signature.
    Signature sig = new Signature(12);

    // Create public key
    PublicKey pubKey = new PublicKey(12);

    int totalRuns = 1000;

    long start = System.currentTimeMillis();
    for (int i = 0; i != totalRuns; ++i) {
      randomIntArray(r,d);
      randomIntArray(r,e);
      randomIntArray(r,k);
      ecc.initializePublicKey(pubKey, d);
            
      boolean b = ecc.signHash(sig, d, e, k);
      if (!b) {
        System.out.println("signHash failed (this has very low probability)");
        continue;
      }

      b = ecc.verifySignature(e, sig, pubKey);
      if (!b) {
        System.out.println("verifySignature failed (this is a bug)");
        break;
      }
    }

    long end = System.currentTimeMillis();
    System.out.println(String.format("Total time (%d sign/verify pairs): %dmsec", totalRuns, end - start));
  }
}
