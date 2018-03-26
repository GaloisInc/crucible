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

public class TestSAWSimulator {
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
    public void testSatPath() throws Exception {
        boolean initSetting = sim.getPathSatChecking();
        sim.setPathSatChecking( !initSetting );
        boolean nextSetting = sim.getPathSatChecking();
	Assert.assertTrue( initSetting != nextSetting );
    }

}
