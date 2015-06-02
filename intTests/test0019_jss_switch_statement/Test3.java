// Unlike 'Test1', 'Test2', and 'FFS', which generate a
// 'lookupswitch' JVM instruction, this code generates a 'tableswitch'
// JVM instruction.

public class Test3 {
  public static void main(String[] args) {
    System.out.println(f(3));
  }

  // Crash.
  static int f(int i) {
    switch (i) {
    case 0: return 0;
    case 1: return 1;
    case 2: return 2;
    case 3: return 3;
    }
    return 4;
  }
}
