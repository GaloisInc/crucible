// Test fall-through switch.
public class Id {
  static int id_imp(int x) {
    int z1 = 0, z2 = 0, z3 = 0;
    switch (x) {
    case 0: case 2: case 4: case 8: case 16: case 32: case 64:
      z1 = x;
      break;
    case 1: case 3: case 5: case 9: case 17: case 33: case 65:
      z2 = x;
      break;
    default:
      z3 = x;
      break;
    }
    return z1 + z2 + z3;
  }
}
