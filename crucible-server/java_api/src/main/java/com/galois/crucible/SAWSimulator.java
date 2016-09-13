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
        Protos.CallResponse r = getNextCallResponse();
    }
}
