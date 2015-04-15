import com.galois.symbolic.*;
class Test {
    public static void main(String[] args) {
        byte x = Symbolic.freshByte((byte)0);
        byte y = Symbolic.freshByte((byte)0);
        Symbolic.writeCnf("tmp/x__x.cnf", x == x);
        Symbolic.writeCnf("tmp/x__x1.cnf", x == x + 1);
        Symbolic.writeCnf("tmp/x__y.cnf", x == y);
        Symbolic.writeCnf("tmp/x_not_y.cnf", x != y);
        Symbolic.writeCnf("tmp/xx_not_2x.cnf", x + x != x * 2);
    }
}
