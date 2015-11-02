import com.galois.symbolic.*;
class Test {
    public static void main(String[] args) {
        byte x = Symbolic.freshByte((byte)0);
        byte y = Symbolic.freshByte((byte)0);
        Symbolic.writeAiger("tmp/x__x.aig" , x == x      , x, y );
        Symbolic.writeAiger("tmp/x__x1.aig", x == x + 1  , x, y );
        Symbolic.writeAiger("tmp/x__y.aig" , x == y      , x, y );
        Symbolic.writeAiger("tmp/xx.aig"   , x + x       , x, y );
        Symbolic.writeAiger("tmp/2x.aig"   , x * 2       , x, y );
        Symbolic.writeAiger("tmp/yy.aig"   , y + y       , x, y );
        Symbolic.writeAiger("tmp/2y.aig"   , y * 2       , x, y );
    }
}
