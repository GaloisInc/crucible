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
 * Main interface to symbolic simulator, using the simple backend.
 */
public final class SimpleSimulator extends Simulator {
    private SimpleSimulator() {}

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
    public static SimpleSimulator launchLocal(String command) throws IOException {
	Process p = Simulator.launchLocalProcess(command);
	SimpleSimulator sim = new SimpleSimulator();
	sim.setupSimulator(p.getOutputStream(), p.getInputStream(), Protos.Backend.SimpleBackend);

	return sim;
    }

    /**
     * This writes an SMTLib2 file to check if <code>x</code> is a satisfiable
     * boolean expression.
     */
    public void writeSmtlib2(String path, SimulatorValue x) throws IOException {
        // Get predefined handle for checkSat.
        FunctionHandle h = getWriteSmtlib2Handle();

        // call function.
        try {
            SimulatorValue res = runCall(h, new StringValue(path), x);
            if (!(res instanceof UnitValue)) {
                throw new Error("writeSmtlib2 did not return a unit variable.");
            }

        } catch (SimulatorFailedException e) {
            throw new Error("Failed to run writeSmtlib2.", e);
        }
    }


    /**
     * This writes a Yices file to check if <code>x</code> is a satisfiable
     * boolean expression.
     */
    public void writeYices(String path, SimulatorValue x) throws IOException {
        // Get predefined handle for checkSat.
        FunctionHandle h = getWriteYicesHandle();

        // call function.
        try {
            SimulatorValue res = runCall(h, new StringValue(path), x);
            if (!(res instanceof UnitValue)) {
                throw new Error("writeYices did not return a unit variable.");
            }

        } catch (SimulatorFailedException e) {
            throw new Error("Failed to run writeYices.", e);
        }
    }


    /**
     * This performs a satisfiability check to determine if <code>x</code> is satisfiable.
     *
     * @return True if value is satisfiable.
     */
    public boolean checkSatWithAbc(SimulatorValue x) throws IOException {
        // Get predefined handle for checkSat.
        FunctionHandle h = getCheckSatWithAbcHandle();

        // call function.
        try {
            SimulatorValue res = runCall(h, x);
            if (!(res instanceof BoolValue)) {
                throw new Error("Check sat did not return a Boolean variable.");
            }

            // Get return value
            return ((BoolValue) res).getValue();
        } catch (SimulatorFailedException e) {
            throw new Error("Failed to run checkSat.", e);
        }
    }

    /**
     * Returns handle associated with checking whether a predicate is
     * true.
     *
     * @throws IOException When there was an error when interacting with
     *         the server.
     * @return the handle
     */
    public FunctionHandle getCheckSatWithAbcHandle() throws IOException {
        return getHandleByName("checkSatWithAbc");
    }
    

    /**
     * This performs a satisfiability check to determine if <code>x</code> is satisfiable.
     *
     * @return True if value is satisfiable.
     */
    public boolean checkSatWithYices(SimulatorValue x) throws IOException {
        // Get predefined handle for checkSat.
        FunctionHandle h = getCheckSatWithYicesHandle();

        // call function.
        try {
            SimulatorValue res = runCall(h, x);
            if (!(res instanceof BoolValue)) {
                throw new Error("Check sat did not return a Boolean variable.");
            }

            // Get return value
            return ((BoolValue) res).getValue();
        } catch (SimulatorFailedException e) {
            throw new Error("Failed to run checkSat.", e);
        }
    }

    /**
     * Returns handle associated with checking whether a predicate is
     * true.
     *
     * @throws IOException When there was an error when interacting with
     *         the server.
     * @return the handle
     */
    public FunctionHandle getCheckSatWithYicesHandle() throws IOException {
        return getHandleByName("checkSatWithYices");
    }

    /**
     * Returns handle associated with writing an SMTLib2 file that asserts
     * a given predicate is true.
     *
     * The function returned expects two arguments.  The first is a
     * string containing the filename to write to.  The second is a
     * Boolean predicate.
     *
     * @return the handle
     */
    public FunctionHandle getWriteSmtlib2Handle() throws IOException {
        return getHandleByName("write_SMTLIB2");
    }

    /**
     * Returns handle associated with writing a Yices file that asserts
     * a given predicate is true.
     *
     * The function returned expects two arguments.  The first is a
     * string containing the filename to write to.  The second is a
     * Boolean predicate.
     *
     * @return the handle
     */
    public FunctionHandle getWriteYicesHandle() throws IOException {
        return getHandleByName("write_yices");
    }

    /**
     * This writes an AIGER file representing the given sequence of
     * symbolic values, each of which should be either a boolean
     * or a bitvector.  Bitvectors are encoded into the AIGER in
     * most-significant-bit first order.
     */
    public synchronized void writeAIGER( String path, SimulatorValue ... vals )
        throws IOException {

        Protos.Request.Builder b
            = Protos.Request.newBuilder()
            .setCode(Protos.RequestCode.ExportModel)
            .setExportFormat(Protos.ExportFormat.ExportAIGER)
            .setExportPath(path);

        for( SimulatorValue v : vals ) {
            b.addArg(v.getValueRep());
        }

        issueRequest(b);

        // Wait for the server to finish
        getNextAckResponse();
    }
}
