public class FFS {
  public static void main(String[] args) {
    System.out.println(ffs_imp(4));
  }

  // Crash.
  static int ffs_imp(int i) {
    switch (((~i) + 1) ^ i) {
    case 0xfffffffe: return 1;
    case 0xfffffffc: return 2;
    case 0xfffffff8: return 3;
    case 0xfffffff0: return 4;
    case 0xffffffe0: return 5;
    case 0xffffffc0: return 6;
    case 0xffffff80: return 7;
    case 0xffffff00: return 8;
    case 0xfffffe00: return 9;
    case 0xfffffc00: return 10;
    case 0xfffff800: return 11;
    case 0xfffff000: return 12;
    case 0xffffe000: return 13;
    case 0xffffc000: return 14;
    case 0xffff8000: return 15;
    case 0xffff0000: return 16;
    case 0xfffe0000: return 17;
    case 0xfffc0000: return 18;
    case 0xfff80000: return 19;
    case 0xfff00000: return 20;
    case 0xffe00000: return 21;
    case 0xffc00000: return 22;
    case 0xff800000: return 23;
    case 0xff000000: return 24;
    case 0xfe000000: return 25;
    case 0xfc000000: return 26;
    case 0xf8000000: return 27;
    case 0xf0000000: return 28;
    case 0xe0000000: return 29;
    case 0xc0000000: return 30;
    case 0x80000000: return 31;
    case 0x00000000: return i == 0 ? 0 : 32;
    }
    return 0; // Unreachable.
  }
}
