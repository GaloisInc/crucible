public class Test2 {
  public static void main(String[] args) {
    System.out.println(f(2));
  }

  // Crash.
  static int f(int i) {
    switch (i) {
    case 0: break;
    case 1: break;
    }
    return 2;
  }
}
