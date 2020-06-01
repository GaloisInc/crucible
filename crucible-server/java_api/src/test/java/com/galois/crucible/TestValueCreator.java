package com.galois.crucible;

import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.rules.ExternalResource;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import com.galois.crucible.proto.Protos;

public class TestValueCreator {
    String simPath = System.getProperty("CRUCIBLE_SERVER");
    SimpleSimulator sim;

    @Rule
    public ExternalResource simResource = new ExternalResource() {
	    @Override
	    protected void before() throws Throwable {
		if( simPath == null ) {
		    throw new Exception( "crucible server executable path not configured!" );
		}

		sim = SimpleSimulator.launchLocal(simPath);
		if( sim == null ) {
		    throw new Exception( "unable to launch crucible server executable" );
		}
	    }

	    @Override
	    protected void after() {
		try {
		    sim.close();
		} catch (Exception e) {
		    e.printStackTrace();
		    System.exit(1);
		}
	    }
    };

    @Test
    public void basicTest() throws Exception {
	SimulatorValue x = new BitvectorValue(8, BigInteger.valueOf(4));
	System.out.format("client: Generated constant: %s\n", x);

	SimulatorValue v = sim.freshConstant(VarType.bitvector(8));

	SimulatorValue r = sim.add(x,x);
	System.out.format("client: Compute x + x: %s\n", r);

	SimulatorValue query = sim.eq(sim.add(v,v), new BitvectorValue(8, BigInteger.valueOf(2)));

	boolean isSat = sim.checkSatWithAbc(query);
	if (isSat) {
	    System.out.println("Satisfiable");
	} else {
	    System.out.println("Unsatisfiable");
	}
    }

    @Test
    public void concatTest() throws Exception {
	SimulatorValue x = sim.bvLiteral( 16, 0xdeadL );
	SimulatorValue y = sim.bvLiteral( 16, 0xbeefL );

	SimulatorValue xy = sim.bvConcat( x, y );
	SimulatorValue yx = sim.bvConcat( y, x );

	Assert.assertTrue( xy.type().equals( Type.bitvector(32) ) );
	Assert.assertTrue( yx.type().equals( Type.bitvector(32) ) );

	BitvectorValue bv_xy = (BitvectorValue) xy;
	BitvectorValue bv_yx = (BitvectorValue) yx;

	Assert.assertTrue( bv_xy.getValue().equals( BigInteger.valueOf( 0xdeadbeefL ) ) );
	Assert.assertTrue( bv_yx.getValue().equals( BigInteger.valueOf( 0xbeefdeadL ) ) );
    }

    @Test
    public void concatTest2() throws Exception {
	SimulatorValue a = sim.bvLiteral( 8, 0xaaL );
	SimulatorValue b = sim.bvLiteral( 8, 0xbbL );
	SimulatorValue c = sim.bvLiteral( 8, 0xccL );
	SimulatorValue d = sim.bvLiteral( 8, 0xddL );

	SimulatorValue abcd = sim.bvConcat( new SimulatorValue[] { a, b, c, d } );
	SimulatorValue dcba = sim.bvConcat( new SimulatorValue[] { d, c, b, a } );

	Assert.assertTrue( abcd.type().equals( Type.bitvector(32) ) );
	Assert.assertTrue( dcba.type().equals( Type.bitvector(32) ) );

	BitvectorValue bv_abcd = (BitvectorValue) abcd;
	BitvectorValue bv_dcba = (BitvectorValue) dcba;

	Assert.assertTrue( bv_abcd.getValue().equals( BigInteger.valueOf( 0xaabbccddL ) ) );
	Assert.assertTrue( bv_dcba.getValue().equals( BigInteger.valueOf( 0xddccbbaaL ) ) );
    }

    @Test
    public void selectTest() throws Exception {
	SimulatorValue x = sim.bvLiteral( 32, 0x0123abcdL );

	SimulatorValue hi  = sim.bvSelect( 16, 16, x );
	SimulatorValue mid = sim.bvSelect( 8, 16, x );
	SimulatorValue lo  = sim.bvSelect( 0, 16, x );

	Assert.assertTrue( hi.type().equals( Type.bitvector(16) ) );
	Assert.assertTrue( mid.type().equals( Type.bitvector(16) ) );
	Assert.assertTrue( lo.type().equals( Type.bitvector(16) ) );

	BitvectorValue bv_hi = (BitvectorValue) hi;
	BitvectorValue bv_mid = (BitvectorValue) mid;
	BitvectorValue bv_lo = (BitvectorValue) lo;

	Assert.assertTrue( bv_hi.getValue().equals( BigInteger.valueOf( 0x0123L ) ) );
	Assert.assertTrue( bv_mid.getValue().equals( BigInteger.valueOf( 0x23abL ) ) );
	Assert.assertTrue( bv_lo.getValue().equals( BigInteger.valueOf( 0xabcdL ) ) );
    }

    @Test
    public void checkSatTest() throws Exception {
	SimulatorValue x = sim.bvLiteral( 8, 12 );
	SimulatorValue y = sim.freshConstant( VarType.bitvector(8) );
	SimulatorValue z = sim.add( x, y );

	SimulatorValue p = sim.eq( z, sim.bvLiteral( 8, 42 ) );
	SimulatorValue q = sim.eq( y, sim.bvLiteral( 8, 30 ) );

	Assert.assertTrue( sim.checkSatWithAbc( p ) );
	Assert.assertTrue( sim.checkSatWithAbc( sim.and( p, q ) ) );
	Assert.assertTrue( sim.checkSatWithAbc( sim.not( q ) ) );
	Assert.assertFalse( sim.checkSatWithAbc( sim.and( p, sim.not( q ) ) ) );
    }

    @Test
    public void concatSelectSat() throws Exception {
	SimulatorValue x = sim.freshConstant( VarType.bitvector(8) );
	SimulatorValue y = sim.bvLiteral( 8, 0xaf );
	SimulatorValue z = sim.bvConcat( y , x );

	SimulatorValue x2 = sim.bvSelect( 0, 8, z );
	SimulatorValue y2 = sim.bvSelect( 8, 8, z );

	SimulatorValue p = sim.not(sim.eq( x, x2 ));
	SimulatorValue q = sim.not(sim.eq( y, sim.bvLiteral( 8, 0xaf )));

	Assert.assertFalse( sim.checkSatWithAbc( p ) );
	Assert.assertFalse( sim.checkSatWithAbc( q ) );
    }

    @Test
    public void testMultipart1() throws Exception {
        // 16-bit addresses and 9-bit words (just for kicks)
        SimulatorValue wm = sim.emptyWordMap( 16, Type.bitvector(9) );
        SimulatorValue val = sim.bvLiteral( 27, 1234567 );
        SimulatorValue addr = sim.bvLiteral( 16, 0xabcd );

        SimulatorValue wm2 = sim.multipartStore( BoolValue.TRUE, addr, val, wm );
        SimulatorValue x   = sim.multipartLoad( BoolValue.TRUE, addr, 3, wm2 );
        SimulatorValue p   = sim.eq( val, x );

        Assert.assertTrue( ((BoolValue) p).equals( BoolValue.TRUE ) );
    }

    @Test
    public void testMultipart2() throws Exception {
        // 16-bit addresses and 9-bit words (just for kicks)
        SimulatorValue wm = sim.emptyWordMap( 16, Type.bitvector(9) );
        SimulatorValue val = sim.bvLiteral( 27, 1234567 );
        SimulatorValue addr = sim.bvLiteral( 16, 0xabcd );

        SimulatorValue wm2 = sim.multipartStore( BoolValue.FALSE, addr, val, wm );
        SimulatorValue x   = sim.multipartLoad( BoolValue.FALSE, addr, 3, wm2 );
        SimulatorValue p   = sim.eq( val, x );

        Assert.assertTrue( ((BoolValue) p).equals( BoolValue.TRUE ) );
    }

};
