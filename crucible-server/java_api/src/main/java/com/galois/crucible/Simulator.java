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

import com.galois.crucible.cfg.Position;
import com.galois.crucible.cfg.Procedure;
import com.google.protobuf.MessageLite;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.MessageConsumer;

/**
 * Main interface to symbolic simulator.
 *
 * <p>
 * Implementation note: Simulator values may be a reference to a value in the
 * server.  The number of values is not expected to be large, but enable
 * server resources to be garbage collected, simulator values containing
 * references use the finalizer to release their resources.  To avoid thread
 * contention, one should synchornize on the <code>Simulator</code> object when
 * sending and receiving messages to the server.
 */
public abstract class Simulator extends ValueCreator<SimulatorValue> {

    /** Event listeners for listening when print is called. */
    private List<MessageConsumer> printMessageListeners = new LinkedList<MessageConsumer>();

    /** Event listeners for listening when path is aborted. */
    private List<MessageConsumer> pathAbortedListeners = new LinkedList<MessageConsumer>();

    /** Responses that have been queued up by the dedicated call response thread */
    private BlockingDeque<Protos.GenericResponse> queuedResponses =
        new LinkedBlockingDeque<Protos.GenericResponse>();
      // FIXME, should this be capacity limited?

    /**
     * The dedicated thread that reads responses from the server and queues them
     * for subsequent proessing
     */
    private Thread responseListenerThread;

    /** Are we in the process of shutting down the connection to the crucible server? */
    private boolean closing = false;

    /** Stream to write any status messages to.  Null indicates no logging */
    private PrintStream statusStream = null;

    /**
     * Set the stream to write logging messages to.
     * @param s The stream.
     */
    public void setStatusStream(PrintStream s) {
        statusStream = s;
    }


    /** Get the next queued server response.  Will block until a response is avaliable. */
    protected Protos.GenericResponse getNextResponse() throws IOException {
        Protos.GenericResponse resp = null;

        // Retry if we get interrupted
        while (true) {
            try {
                resp = queuedResponses.takeFirst();

                switch(resp.getCode()) {
                case ExceptionGenResp:
                    // If the response is an exception, raise a corresponging
                    // exception.
                    String msg = resp.getMessage();
                    throw new IOException( msg );
                default:
                    // Otherwise, return the response
                    return resp;
                }
            } catch (InterruptedException ex) {
            }
        }
    }

    protected void getNextAckResponse() throws IOException {
        Protos.GenericResponse r = getNextResponse();

        switch(r.getCode()) {
        case AcknowledgementResp:
            return;
        }

        throw new IOException( "Expected simulator ACK response!\n" + r.toString() );
    }

    protected Protos.SimulatorValueResponse getNextSimulatorValueResponse() throws IOException {
        Protos.GenericResponse r = getNextResponse();
        Protos.SimulatorValueResponse svr = r.getSimValResponse();

        switch(r.getCode()) {
        case SimulatorValueGenResp:
            if( svr != null ) {
                return svr;
            }
        }

        throw new IOException( "Expected simulator value response!" + r.toString() );
    }

    protected Protos.RegisterHandleResponse getNextRegisterHandleResponse() throws IOException {
        Protos.GenericResponse r = getNextResponse();
        Protos.RegisterHandleResponse hr = r.getRegHandleResponse();

        switch(r.getCode()) {
        case RegisterHandleGenResp:
            if( hr != null ) {
                return hr;
            }
        }

        throw new IOException( "Expected register handle response!" + r.toString() );
    }

    protected Protos.PredefinedHandleInfo getNextPredefHandleResponse() throws IOException {
        Protos.GenericResponse r = getNextResponse();
        Protos.PredefinedHandleInfo hi = r.getPredefHandleResponse();

        switch(r.getCode()) {
        case PredefHandleGenResp:
            if( hi != null ) {
                return hi;
            }
        }

        throw new IOException( "Expected predefined handle info!" + r.toString() );
    }

    protected Protos.CallResponse getNextCallResponse() throws IOException {
        Protos.GenericResponse r = getNextResponse();
        Protos.CallResponse cr = r.getCallResponse();

        switch(r.getCode()) {
        case CallGenResp:
            if( cr != null ) {
                return cr;
            }
        }

        throw new IOException( "Expected call response!" + r.toString() );
    }

    /**
     * Start a dedicated thread to read responses from the crucible server.
     * Responses that print values are immediately handed off to the printMessageListeners,
     * and other responses are queued into the queuedResponses list.
     *
     * This thread exits when the associated stream is closed.  If the <code>closing</code>
     * flag is not set, this will cause a message to be printed and an immediate JVM exit.
     */
    private void startResponseListenerThread() {
        final Simulator sim = this;
        responseListenerThread = new Thread() {
                public void run() {
                    try {
                        while(true) {
                            Protos.GenericResponse r =
                                Protos.GenericResponse.parseDelimitedFrom(response);

                            // null return generally indicates the input stream was closed
                            if( r == null ) { break; }

                            switch (r.getCode()) {
                            case PrintGenResp:
                                SimulatorMessage msg = new SimulatorMessage( r.getMessage() );

                                synchronized(printMessageListeners) {
                                    for (MessageConsumer p : printMessageListeners) {
                                        p.acceptMessage(msg);
                                    }
                                }
                                break;
                            default:
                                queuedResponses.putLast(r);
                            }
                        }
                    } catch (InterruptedException ex) {
                    } catch (Exception ex) {
                        ex.printStackTrace();
                    }
                    System.err.println("response listener thread exiting");

                    synchronized(sim) {
                        if(!sim.closing) {
                            System.err.println("response stream closed unexpectedly!");
                            System.exit(1);
                        }
                    }
                }
            };

        responseListenerThread.start();
    }

    private static class OverrideEntry {
        OverrideEntry(FunctionHandle h, SimulatorFunction fn) {
            this.h = h;
            this.fn = fn;
        }

        final FunctionHandle h;
        final SimulatorFunction fn;
    }

    /**
     * Maps handle indices that are overriden to the function
     * implementing their behavior.
     */
    private HashMap<Long, OverrideEntry> overrideMap
      = new HashMap<Long, OverrideEntry>();

    /**
     * Flag to indicates that requests are suspended.  This is only set to
     * true when the simulator is running a potentially long-running computation
     * that it expects a response from before sending a new request.
     *
     * When this is true, the thread should wait until it is ready.
     * Invariants:
     *   When <code>request</code> is <code>null</code>, this should be <code>true</code>.
     */
    private boolean requestSuspended;

    /**
     * This indicates the number of overrides that we are inside of
     * when executing functions.
     *
     * It should be 0 when we are not currently executing a call.
     */
    private long callHeight;

    /**
     * Output stream for issuing requests to simulator.
     */
    private OutputStream request;

    /**
     * Input stream for receiving information to simulator.
     */
    private InputStream response;

    /**
     * The list of symbolic value references that need to be released once
     * the current method is complete.
     */
    private List<Long> releasedReferences = new LinkedList<Long>();

    /**
     * This is an inputstream attached to a process that will throw an exception if
     * an attempt is made to read from it and the process has terminated.
     */
    // FIXME, this class seems unneeded now...
    private static class ProcessInputStream extends InputStream {
        Process p;
        ProcessInputStream(Process p ) {
            this.p = p;
        }
        public int read() throws IOException {
            int r = p.getInputStream().read();
            if (r == -1) {
                String msg = String.format("Server process terminated prematurely (exit code %d)",
                                           p.exitValue());
                throw new IOException(msg);
            }
            return r;
        }
    }

    public static List<String> extraLocalCommandArguments = null;

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
    protected static Process launchLocalProcess(String command) throws IOException {
        if (command == null)
            throw new NullPointerException("command");
        if (command == "")
            throw new IllegalArgumentException("command");

        List<String> commandList = new LinkedList<String>();
        commandList.add(command);
        if( extraLocalCommandArguments != null ) {
            commandList.addAll( extraLocalCommandArguments );
        }
        final Process p = new ProcessBuilder(commandList).start();

        Runnable err_task = new Runnable(){
                public void run(){
                    try {

                      InputStreamReader isr = new InputStreamReader(p.getErrorStream(), "UTF-8");
                      BufferedReader r = new BufferedReader(isr);
                      while (true) {
                        String s = r.readLine();
                        if (s == null) {
                            System.err.format("crucible-server terminated\n");
                            return;
                        }
                        System.err.format("crucible-server: %s%n", s);
                      }
                    } catch (IOException e) {
                        System.err.format("crucible-server error: %s%n", e.getMessage());
                    }
                }
            };
        new Thread(err_task).start();

        return p;
    }

    /**
     * Create a connection to the simulator that will transmit requests
     * over the <code>request</code> stream, and receive responses to
     * the <code>response</code> stream.
     *
     * The simulator requires exclusive access to the streams during
     * execution, and the server must be in an idle state.
     *
     * @param request Stream to use sending requests to crucible-server.
     * @param response Stream to use for receiving responses from crucible-server.
     */
    protected void setupSimulator(OutputStream request, InputStream response, Protos.Backend backend)
        throws java.io.IOException
    {
        synchronized (this) {
            this.requestSuspended = false;
            this.callHeight = 0;
            this.request = request;
            this.response = response;

            Protos.HandShakeRequest.newBuilder()
                .setBackend(backend)
                .build()
                .writeDelimitedTo(request);
            request.flush();

            Protos.HandShakeResponse r =
                Protos.HandShakeResponse.parseDelimitedFrom(response);

            if( r != null && r.getCode() != null &&
                r.getCode().equals( Protos.HandShakeCode.HandShakeOK ) ) {

                // start the listener thread that will parses and queues server responses
                startResponseListenerThread();
            } else {
                String msg = null;
                if( r != null ) { msg = r.getMessage(); }
                if( msg != null ) {
                    msg = "Failed to start simulator: " + msg;
                } else {
                    msg = "Failed to start simulator";
                }
                throw new IOException( msg );
            }
        }
    }

    /**
     * Forcibly terminate a connection.
     */
    private synchronized void forceTerminateConnection() {
        request = null;
        releasedReferences = null;
    }

    private void logStatus(String msg) {
        if (statusStream != null) {
            statusStream.printf("crucible-client: %s\n", msg);
            statusStream.flush();
        }
    }

    /**
     * Close the connection to crucible-server so that no more requests will be sent.
     * @throws InterruptedException If thread is interrupted before closing.
     */
    public void close() throws InterruptedException, IOException {
        synchronized(this) {
            // Wait until we can send a request.
            while (requestSuspended) {
                this.wait();
            }

            closing = true;

            if (request != null) {
                try {
                    logStatus("Sending KillSimulator message.");
                    // Send notice to simulator to end.
                    Protos.Request.newBuilder()
                        .setCode(Protos.RequestCode.KillSimulator)
                        .build()
                        .writeDelimitedTo(request);
                    request.flush();
                } finally {
                    forceTerminateConnection();
                }
            }
        }

        // ask the response listener to shut down
        responseListenerThread.interrupt();

        // wait a short while for the response listener thread
        responseListenerThread.join(100);
    }

    /**
     * Build message and write it to crucible-server.
     * The simulator should own a lock to this when issueRequest is called.
     */
    protected void issueRequest(Protos.Request.Builder msg) {
        // Wait until we can send a request.
        while (requestSuspended) {
            try {
                this.wait();
            } catch (InterruptedException e) {
                throw new SimulatorFailedException(e);
            }
        }

        if (request == null)
            throw new UnsupportedOperationException("Simulator has been closed.");
        try {
            logStatus("Sending request: " + msg.getCode().toString());
            msg.build().writeDelimitedTo(request);
            request.flush();
        } catch (IOException e) {
            forceTerminateConnection();
            throw new SimulatorFailedException(e);
        }
    }

    /**
     * Release a reference value, or schedule it to be released.
     */
    synchronized void releaseReferenceValue(long index)
        throws IOException {
        if (request == null) return;

        if (requestSuspended) {
            releasedReferences.add(new Long(index));
        } else {
            Protos.Request.newBuilder()
                .setCode(Protos.RequestCode.ReleaseValue)
                .setIndex(index)
                .build()
                .writeDelimitedTo(request);
            request.flush();
        }
    }

    /**
     * Start call.
     */
    private synchronized void startCall(SimulatorValue f, SimulatorValue[] args)
    throws IOException {
        if (request == null)
            throw new UnsupportedOperationException("Simulator has been finalized.");

        // Disable requests until call is complete.
        requestSuspended = true;


        Protos.Request.Builder b
            = Protos.Request.newBuilder()
            .setCode(Protos.RequestCode.RunCall)
            .addArg(f.getValueRep());
        for (SimulatorValue v : args) {
            b.addArg(v.getValueRep());
        }
        b.build()
         .writeDelimitedTo(request);
        request.flush();
    }

    /**
     * End call
     */
    private synchronized void endCall() throws IOException {
        if (request != null) {
            requestSuspended = false;
            // wake up the threads blocked waiting for requests to resume
            this.notifyAll();

            // Release any references that were queued up during call.
            while (releasedReferences.size() > 0) {
                Long ref = releasedReferences.remove(0);
                Protos.Request.newBuilder()
                    .setCode(Protos.RequestCode.ReleaseValue)
                    .setIndex(ref.longValue())
                    .build()
                    .writeDelimitedTo(request);
            }
            request.flush();
        }
    }

    private
    void respondToOverrideCalled(long handle_index, List<Protos.Value> args) {
        OverrideEntry e = overrideMap.get(new Long(handle_index));
        if (e == null)
            throw new IllegalStateException("Simulator asked to respond to undefined override.");
        FunctionHandle h = e.h;
        if (h.getArgCount() != args.size()) {
            throw new IllegalStateException("Override given incorrect number of arguments.");
        }

        SimulatorValue[] argArray = new SimulatorValue[args.size()];
        for (int i = 0; i != args.size(); ++i) {
            Type tp = h.getArgType(i);
            argArray[i] = fromProtosValue(args.get(i), tp);
        }

        ++callHeight;
        SimulatorValue r = e.fn.run(argArray);
        --callHeight;

        // Tell simulator to resume execution.
        synchronized (this) {
            issueRequest(Protos.Request.newBuilder()
                         .setCode(Protos.RequestCode.ResumeSimulation)
                         .setReturnValue(r.getValueRep()));
        }
    }

    /**
     * Runs a procedure call.
     * @throws SimulatorFailedException When simulation fails on all execution paths.
     */
    public SimulatorValue runCall(SimulatorValue f, SimulatorValue ... args) {
        Type f_type = f.type();
        if (!f_type.isFunctionHandle()) {
            throw new IllegalArgumentException("runCall expects a function.");
        }

        if (f_type.getFunctionArgumentCount() != args.length) {
            throw new IllegalArgumentException("runCall given incorrect number of arguments.");
        }

        // Check function arguments.
        for (int i = 0; i != args.length; ++i) {
            Type arg_type = args[i].type();
            Type expected_type = f_type.getFunctionArgumentType(i);
            if (!arg_type.equals(expected_type)) {
                String msg = String.format("runCall argument $1 has incorrect type.", i);
                throw new IllegalArgumentException(msg);
            }
        }

        Type return_type = f_type.getFunctionReturnType();

        List<SimulatorMessage> abortedMessages = new LinkedList<SimulatorMessage>();

        try {
            try {
                startCall(f, args);
                while (true) {
                    Protos.CallResponse r = getNextCallResponse();

                    switch (r.getCode()) {
                    case CallOverrideCalled:
                        respondToOverrideCalled(r.getHandleIndex(), r.getArgList());
                        break;
                    case CallPathAborted:
                        SimulatorMessage msg =
			    SimulatorMessage.parsePathAbortedMessage( r.getMessage() );

                        abortedMessages.add( msg );
                        for (MessageConsumer p : pathAbortedListeners) {
                            p.acceptMessage(msg);
                        }
                        break;
                    case CallReturnValue:
                        return fromProtosValue(r.getReturnVal(), return_type);
                    case CallAllAborted:
                        throw new SimulatorAbortedException( abortedMessages );
                    default:
                        // Kill request since we can't expect to parse results again.
                        forceTerminateConnection();
                        throw new SimulatorFailedException("Could not parse simulator response: " + r.toString() );
                    }
                }
            } finally {
                endCall();
            }
        } catch (IOException e) {
            forceTerminateConnection();
            throw new SimulatorFailedException(e);
        }

    }


    public SimulatorValue boolLiteral( boolean val )
    {
        if( val ) {
            return BoolValue.TRUE;
        } else {
            return BoolValue.FALSE;
        }
    }

    public SimulatorValue bvLiteral( long width, BigInteger val )
    {
        return new BitvectorValue( width, val );
    }

    public SimulatorValue natLiteral( BigInteger val )
    {
        return new NatValue( val );
    }

    public SimulatorValue callHandle( FunctionHandle hdl, Object... args ) {
        return runCall( hdl, Arrays.copyOf( args, args.length, SimulatorValue[].class ) );
    }

    protected
    synchronized
    SimulatorValue applyPrimitive(Type type,
                                  Protos.PrimitiveOp op,
                                  Object... args) {

        Protos.Request.Builder b
            = Protos.Request.newBuilder()
            .setCode(Protos.RequestCode.ApplyPrimitive)
            .setPrimOp(op)
            .setResultType(type.getTypeRep());
        for (Object v : args) {
            b.addArg(((SimulatorValue) v) .getValueRep());
        }
        issueRequest(b);

        try {
            Protos.SimulatorValueResponse r = getNextSimulatorValueResponse();

            if (!r.getSuccessful()) {
                String msg = "Could not create simulator value";
                String err = r.getErrorMsg();
                if( !(err == null) ) { msg = msg + ": " + err; }
                throw new SimulatorFailedException(msg);
            }

            // Parse value back.
            return fromProtosValue(r.getValue(), type);
        } catch (IOException e) {
            throw new SimulatorFailedException(e);
        }
    }

    /**
     * Tell the simulator to use the given procedure when calling
     * functions with the handle associated to the procedure.
     *
     * @param p procedure to use
     */
    public synchronized void useCfg(Procedure p) throws IOException {
        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.UseCFG)
                     .setCfg(p.getCfgRep()));
        getNextAckResponse();
    }

    /**
     * Tell the simulator to unpack and print the given CFG.
     *
     * @param p procedure to use
     */
    public synchronized void printCFG(Procedure p) throws IOException {
        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.PrintCFG)
                     .setCfg(p.getCfgRep()));
        getNextAckResponse();
    }

    /**
     * Tell the simulator to call Java code when the function
     * <code>h</code> is called.
     * This replaces any current binding to the handle.
     *
     * @param h The handle to attach the override to.
     * @param f The Java function to run when the function is called.
     */
    public synchronized
    void useOverride(FunctionHandle h, SimulatorFunction f ) {

        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.UseOverride)
                     .setIndex(h.getUniqueId()));
        // Add override to map for later lookup.
        overrideMap.put(h.getUniqueId(), new OverrideEntry(h, f));
    }

    /**
     * Add listener that receives evens when message is printed during symbolic execution.
     */
    public void addPrintMessageListener(MessageConsumer listener) {
        synchronized(printMessageListeners) {
            printMessageListeners.add(listener);
        }
    }

    /**
     * Add listener that receives evens when path is aborted during symbolic execution.
     */
    public synchronized void addPathAbortedListener(MessageConsumer listener) {
        pathAbortedListeners.add(listener);
    }

    /** Read a simulator value from the protocol buffer format. */
    protected static
    SimulatorValue fromProtosValue(Protos.Value v, Type expectedType) {
        // Declare local variables so intance variables are assigned once.
        switch (v.getCode()) {
        case ReferenceValue:
            return new ReferenceValue(expectedType, v.getIndex());
        case TrueValue:
            if (!expectedType.equals(Type.BOOL))
                throw new IllegalArgumentException("Expected bool value.");
            return BoolValue.TRUE;
        case FalseValue:
            if (!expectedType.equals(Type.BOOL))
                throw new IllegalArgumentException("Expected bool value.");
            return BoolValue.FALSE;
        case NatValue:
            // Use big-endian encoding without sign-bit.
            return new NatValue(new BigInteger(1, v.getData().toByteArray()));
        case IntegerValue:
            return new IntegerValue(new BigInteger(v.getData().toByteArray()));
        case RationalValue:
            return new RationalValue(v.getData().toByteArray());
        case BitvectorValue:
            // valueRef stores the width when this is a bitvector.
            return new BitvectorValue(v.getWidth(), new BigInteger(1, v.getData().toByteArray()));
        case StringValue:
            return new StringValue(v.getStringLit());
        case UnitValue:
            if (!expectedType.equals(Type.UNIT))
                throw new IllegalArgumentException("Expected unit value.");
            return new UnitValue();
        case FnHandleValue:
            return new FunctionHandle(v.getIndex(), v.getHandleInfo());
        default:
            throw new IllegalArgumentException("Cannot parse Value kind.");
        }
    }

    /** method for registering a Handle with the simulator. */
    public synchronized
    FunctionHandle
    newHandle(String displayName, Type[] argTypes, Type returnType) throws IOException {
        Protos.HandleInfo.Builder b
            = Protos.HandleInfo.newBuilder()
            .setDisplayName(displayName)
            .setReturnType(returnType.getTypeRep());
        for (Type argType : argTypes) {
            b.addArgType(argType.getTypeRep());
        }
        Protos.HandleInfo h = b.build();

        // Issue request to register handle.
        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.RegisterHandle)
                     .setHandle(h));
        long handleId = getNextRegisterHandleResponse().getIndex();
        return new FunctionHandle(handleId, displayName, argTypes, returnType);
    }

    protected FunctionHandle predefinedHandleInfoResponse() throws IOException {

        Protos.PredefinedHandleInfo pinfo = getNextPredefHandleResponse();

        long handleId = pinfo.getRef();
        Protos.HandleInfo h = pinfo.getInfo();
        // Return handle
        return new FunctionHandle(handleId, h);
    }


    /**
     * Set the verbosity level of the simulator.  Higher verbosity levels
     * generate more informational and debugging messages.
     *
     * @param v The verbosity level.  Valid values are in the range 0..10
     */
    public synchronized void setVerbosity(int v) throws IOException {
        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.SetVerbosity)
                     .addArg(this.natLiteral(v).getValueRep()));
        getNextAckResponse();
    }

    /**
     * Returns handle associated with getting a symbolic variable of the
     * given type.  If a list of dimensions are provided, the returned handle
     * will generate a fresh array of the given base type with the given dimensions.
     *
     * @throws IOException When there was an error when interacting with
     *         the server.
     * @return the handle
     */
    public synchronized FunctionHandle getSymbolicHandle(VarType type)
	throws IOException {

	Protos.Request.Builder b = Protos.Request.newBuilder()
               .setCode(Protos.RequestCode.SymbolicHandle)
               .setVarType(type.getProtosRep());

        issueRequest(b);
        return predefinedHandleInfoResponse();
    }

    /**
     * This creates a new uninterpreted constant with the type
     * <code>type</code>.
     *
     * @param type the type of fresh constants.
     * @return the new constant.
     */
    public SimulatorValue freshConstant(VarType type) throws IOException {
        try {
            return runCall(getSymbolicHandle(type));
        } catch (SimulatorFailedException e) {
            throw new Error("Failed to create symbolic variable.", e);
        }
    }


    /**
     * Returns a predefined function handle with the given name.
     *
     * @throws IOException When there was an error when interacting with
     *         the server.  In particular, if a function with the given
     *         name is not found, an exception will be thrown.
     * @return the handle
     */
    public synchronized FunctionHandle getHandleByName( String name ) throws IOException {
        Protos.HandleInfo h =
          Protos.HandleInfo.newBuilder()
          .setDisplayName(name)
          .build();

        issueRequest(Protos.Request.newBuilder()
                      .setCode(Protos.RequestCode.GetHandleByName)
                      .setHandle(h) );

        return predefinedHandleInfoResponse();
    }

    public synchronized FunctionHandle getMultipartStoreHandle( long addrWidth, long cellWidth, long parts )
        throws IOException {

        Type[] argTypes = {
            Type.BOOL,
            Type.bitvector( addrWidth ),
            Type.bitvector( cellWidth * parts ),
            Type.wordMap( addrWidth, Type.bitvector( cellWidth ) ),
            };
        Type returnType = Type.wordMap( addrWidth, Type.bitvector( cellWidth ) );

        Protos.HandleInfo.Builder h
            = Protos.HandleInfo.newBuilder()
            .setReturnType(returnType.getTypeRep());
        for (Type tp : argTypes) {
            h.addArgType(tp.getTypeRep());
        }
        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.MultipartStoreHandle)
                     .setHandle(h.build()) );

        return predefinedHandleInfoResponse();
    }

    public synchronized FunctionHandle getMultipartLoadHandle( long addrWidth, long cellWidth, long parts )
        throws IOException {

        Type[] argTypes = {
            Type.BOOL,
            Type.bitvector( addrWidth ),
            Type.wordMap( addrWidth, Type.bitvector( cellWidth ) ),
            Type.maybe( Type.bitvector( cellWidth ) )
        };
        Type returnType = Type.bitvector( cellWidth * parts );

        Protos.HandleInfo.Builder h =
            Protos.HandleInfo.newBuilder()
            .setReturnType(returnType.getTypeRep());
        for (Type tp : argTypes) {
            h.addArgType(tp.getTypeRep());
        }

        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.MultipartLoadHandle)
                     .setHandle(h.build()) );

        return predefinedHandleInfoResponse();
    }

    public SimulatorValue multipartStore( SimulatorValue isBigEndian,
                                          SimulatorValue addr,
                                          SimulatorValue val,
                                          SimulatorValue map )
        throws IOException {

        long addrWidth = addr.type().width();
        long cellWidth = map.type().wordMapRangeType().width();
        long parts     = val.type().width() / cellWidth;

        FunctionHandle storeHandle = getMultipartStoreHandle( addrWidth, cellWidth, parts );

        return runCall( storeHandle, isBigEndian, addr, val, map );
    }

    public SimulatorValue multipartLoad( SimulatorValue isBigEndian,
                                         SimulatorValue addr,
                                         int parts,
                                         SimulatorValue map )
        throws IOException {

        long addrWidth = addr.type().width();
        long cellWidth = map.type().wordMapRangeType().width();

        FunctionHandle loadHandle = getMultipartLoadHandle( addrWidth, cellWidth, parts );

        return runCall( loadHandle, isBigEndian, addr, map, nothingValue(map.type().wordMapRangeType()) );
    }

    public SimulatorValue multipartLoadWithDefault( SimulatorValue isBigEndian,
                                                    SimulatorValue addr,
                                                    int parts,
                                                    SimulatorValue map,
                                                    SimulatorValue def )
        throws IOException {

        long addrWidth = addr.type().width();
        long cellWidth = map.type().wordMapRangeType().width();

        FunctionHandle loadHandle = getMultipartLoadHandle( addrWidth, cellWidth, parts );

        return runCall( loadHandle, isBigEndian, addr, map, justValue(def) );
    }

    /**
     * Returns a predefined function handle for printing terms of the given type.
     * @throws IOException When there was an error when interacting with
     *         the server.  In particular, if the given type cannot be printed,
     *         an exception will be thrown.
     * @return the handle
     */
    public synchronized FunctionHandle getPrintTermHandle( Type tp ) throws IOException {
        issueRequest(Protos.Request.newBuilder()
                     .setCode(Protos.RequestCode.PrintTermHandle)
                     .setType( tp.getTypeRep() ));

        return predefinedHandleInfoResponse();
    }

    /**
     * Causes the crucible simulator to print the given value.
     * @throws IOException If the value cannot be printed.
     */
    public void printTerm( SimulatorValue value ) throws IOException {
        FunctionHandle printTerm = getPrintTermHandle( value.type() );
        runCall( printTerm, value );
    }

}
