// This software is subject to the terms of the IBM Jikes Test Suite
// License Agreement available at the following URL:
// http://www.ibm.com/research/jikes.
// Copyright (C) 1996, 1999, International Business Machines Corporation
// and others.  All Rights Reserved.
// You must accept the terms of that agreement to use this software.

public final class Main {
//  public static int i;
  public static void main(String argv[]) {
      int i = ifunc("bc");
      System.out.println(i);
   }
 static int ifunc( String x2 ) {
    int isum = 0;

    if (x2 == "bc") isum = isum + 1;
    
    return isum;

  }
}

