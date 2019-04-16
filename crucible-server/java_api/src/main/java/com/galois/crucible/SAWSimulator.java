package com.galois.crucible;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.BlockingDeque;
import java.util.concurrent.LinkedBlockingDeque;

import com.galois.crucible.cfg.Procedure;
import com.google.protobuf.MessageLite;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.MessageConsumer;

/**
 * Main interface to symbolic simulator, using the SAW backend.
 */
public final class SAWSimulator extends Simulator {
    private SAWSimulator() {}

     /**
     * Launch a local connection to the simulator.
     *
     * @param command The command to run.
     * @throws SecurityException If a security manager exists and its
     *   {@link java.lang.SecurityManager#checkExec checkExec} method doesn't allow
     *    creation of the subprocess
     * @throws IOException If an I/O error occurs
     * @throws NullPointerException If command is null
     * @throws IllegalArgumentException If command is empty
     * @return A freshly created symbolic simulator interface.
     */
    public static SAWSimulator launchLocal(String command) throws IOException {
	Process p = Simulator.launchLocalProcess(command);
	SAWSimulator sim = new SAWSimulator();
	sim.setupSimulator(p.getOutputStream(), p.getInputStream(), Protos.Backend.SAWBackend);

	return sim;
    }

    /**
     * Set whether path satisfiablity checking is enabled in the symbolic simulator.
     *
     * @param pathSat The new setting value
     * @throws IOException If an I/O error occurs while communicating with the crucible server.
     */
    public synchronized void setPathSatChecking( boolean pathSat ) throws IOException {
        SimulatorValue pathSatVal = pathSat ? BoolValue.TRUE : BoolValue.FALSE;

        issueRequest( Protos.Request.newBuilder()
                      .setCode( Protos.RequestCode.SetConfigValue )
                      .setConfigSettingName( "checkPathSat" )
                      .addArg( pathSatVal.getValueRep() ) );

        getNextAckResponse();
    }

    /**
     * Get whether path satisfiablity checking is currently enabled in the symbolic simulator.
     *
     * @returns The current setting of the path satisfiability configuration value.
     * @throws IOException If an I/O error occurs while communicating with the crucible server.
     * @throws SimulatorFailedException if an unexpected (non-boolean) value is returned by the server.
     */
    public synchronized boolean getPathSatChecking() throws IOException {
        issueRequest( Protos.Request.newBuilder()
                      .setCode(Protos.RequestCode.GetConfigValue)
                      .setConfigSettingName( "checkPathSat" ) );

        Protos.SimulatorValueResponse r = getNextSimulatorValueResponse();

        if (!r.getSuccessful()) {
            String msg = "Could not create simulator value";
            String err = r.getErrorMsg();
            if( !(err == null) ) { msg = msg + ": " + err; }
            throw new SimulatorFailedException(msg);
        }

        // Parse value back.
        SimulatorValue v = fromProtosValue(r.getValue(), Type.BOOL);
        if( v instanceof BoolValue ) {
            BoolValue bv = (BoolValue) v;
            return bv.getValue();
        } else {
            String msg = "Expected boolean value response from simulator when retrieving path sat checking configuration value";
            throw new SimulatorFailedException(msg);
        }
    }

    public synchronized
    FunctionHandle compileHarness( VerificationHarness harness ) throws IOException {
        issueRequest( Protos.Request.newBuilder()
                      .setCode(Protos.RequestCode.CompileVerificationOverride)
                      .setVerificationHarness( harness.getRep() ));

        return predefinedHandleInfoResponse();
    }


    public synchronized void produceVerificationGoals( VerificationHarness harness, VerificationOptions verifOpts )
        throws IOException
    {
        issueRequest( Protos.Request.newBuilder()
                      .setCode(Protos.RequestCode.SimulateVerificationHarness)
                      .setVerificationHarness(harness.getRep())
                      .setVerificationSimOptions(verifOpts.getRep()) );

        // Wait for the server to finish
        getNextAckResponse();
    }


    /**
     * This writes a SAWCore file representing the given sequence of
     * symbolic values.
     */
    public synchronized void writeSAW( String path, SimulatorValue ... vals )
        throws IOException {

        Protos.Request.Builder b
            = Protos.Request.newBuilder()
            .setCode(Protos.RequestCode.ExportModel)
            .setExportFormat(Protos.ExportFormat.ExportSAW)
            .setExportPath(path);

        for( SimulatorValue v : vals ) {
            b.addArg(v.getValueRep());
        }

        issueRequest(b);

        // Wait for the server to finish
        getNextAckResponse();
    }
}
