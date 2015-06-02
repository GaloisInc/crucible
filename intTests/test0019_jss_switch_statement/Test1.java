public class Test1 {
  public static void main(String[] args) {
    System.out.println(f(1));
  }

  // No crash.
  static int f(int i) {
    switch (i) {
    case 0: break;
    }
    return 1;
  }
}
