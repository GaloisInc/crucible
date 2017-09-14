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
        sim.addPrintMessageListener(new MessageConsumer(){
                public void acceptMessage(SimulatorMessage msg) {
                    System.out.println(msg.toString());
                }
            });

        VerificationHarness harness = new VerificationHarness("testHarness");
        Protos.VariableReference constValue   = harness.prestate().addVar( "constValue", 64 );
        Protos.VariableReference testVar      = harness.prestate().addVar( "testVar", 16 );
        Protos.VariableReference testArray    = harness.prestate().addVar( "testArray", 100, 32 );
        Protos.VariableReference poststateVar = harness.poststate().addVar( "poststateVar", 5, 24 );

        harness.prestate().assignRegister( 0x0, constValue );
        harness.prestate().assignRegister( 0x8, harness.returnVar );
        harness.prestate().bindVariable( constValue, "~zero" );

        harness.poststate().assignMemory( VerificationHarness.stackVar, 0x10, poststateVar );
        harness.poststate().assertCondition( "poststateVar == [0,1,2,3,4]" );

        sim.compileHarness( harness );
    }

};
