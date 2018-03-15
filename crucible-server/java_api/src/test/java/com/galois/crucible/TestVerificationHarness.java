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

public class TestVerificationHarness {
    String simPath = System.getProperty("CRUCIBLE_SERVER");
    SAWSimulator sim;

    @Rule
    public ExternalResource simResource = new ExternalResource() {
	    @Override
	    protected void before() throws Throwable {
		if( simPath == null ) {
		    throw new Exception( "crucible server executable path not configured!" );
		}

		sim = SAWSimulator.launchLocal(simPath);
		if( sim == null ) {
		    throw new Exception( "unable to launch crucible server executable" );
		}
                sim.addPrintMessageListener(new MessageConsumer(){
                        public void acceptMessage(SimulatorMessage msg) {
                            System.out.println(msg.toString());
                        }
                    });
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
    public void testVerificationHarness() throws Exception {
        VerificationHarness harness = new VerificationHarness("testHarness", 14, 64, Protos.Endianness.LittleEndian);
        Protos.VariableReference constValue   = harness.prestate().addVar( "constValue", 64 );
        Protos.VariableReference testVar      = harness.prestate().addVar( "testVar", 16 );
        Protos.VariableReference testArray    = harness.prestate().addVar( "testArray", 100, 32 );
        Protos.VariableReference poststateVar = harness.poststate().addVar( "poststateVar", 5, 24 );

        harness.prestate().assignRegister( 0x0, constValue );
        harness.prestate().assignRegister( 0x8, harness.returnVar );
        harness.prestate().assignRegister( 0xf, harness.stackVar );
        harness.prestate().bindVariable( constValue, "~zero" );
        harness.prestate().assignMemory( VerificationHarness.stackVar, 0x00, testArray );
        harness.prestate().bindVariable( testVar, "take (testArray @ constValue)");

        harness.prestate().assertCondition( "testVar == 0xabcd" );

        Protos.VariableReference poststateStack = harness.poststate().addVar( "poststateStack", 64 );

        harness.poststate().assignMemory( VerificationHarness.stackVar, 0x10, poststateVar );
        harness.poststate().bindVariable( poststateVar, "[0,1,2,3,4]" );
        harness.poststate().bindVariable( poststateStack, "stack + 8");
        harness.poststate().assignRegister( 0xf, poststateStack );

        sim.compileHarness( harness );
    }

    // @Test
    // public void bogusVerificationHarness() throws Exception {
    //     VerificationHarness harness = new VerificationHarness("bogusHarness", 64, Protos.Endianness.LittleEndian);
    //     Protos.VariableReference bogus1 = harness.prestate().addVar( "bogus1", 64 );
    //     Protos.VariableReference bogus2 = harness.prestate().addVar( "bogus2", 64 );

    //     harness.prestate().bindVariable( bogus1, "bogus2" );
    //     //        harness.prestate().bindVariable( bogus2, "bogus1" );

    //     sim.compileHarness( harness );
    // }

};
