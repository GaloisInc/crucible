import com.galois.symbolic.*;
class Test {
    static byte exp_ref(byte x, byte p) {
        byte r = 1;
        if (p < 0) {
            return r;
        }

        while (p-- != 0) {
            r *= x;
        }
        return r;
    }

    static byte exp_opt(byte x, byte p) {
        byte r = 1;
        if (p < 0) {
            return r;
        }

        for (; p != 0; x *= x, p >>= 1) {
            if ((p & 1) != 0) {
                r *= x;
            }
        }
        return r;
    }

    public static void main(String[] args) {
        //test();
        byte x = Symbolic.freshByte((byte)0);
        byte y = Symbolic.freshByte((byte)0);
        Symbolic.writeCnf("tmp/exp.cnf", exp_ref(x,y) != exp_opt(x,y));
    }

    static void test() {
        byte x = -128;
        byte p = -128;
        do {
            do {
                if (exp_ref(x,p) != exp_opt(x,p)) {
                    throw new RuntimeException("Counterexample: " + x + " " + p);
                }
            } while (++p != -128);
        } while (++x != -128);
    }
}
