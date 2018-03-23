package com.galois.crucible;

import com.galois.crucible.cfg.Procedure;
import com.galois.crucible.proto.Protos;

public class VerificationOptions {
    private Protos.VerificationSimulateOptions.Builder opts;

    public VerificationOptions() {
        opts = Protos.VerificationSimulateOptions.newBuilder();
        opts.setSeparateObligations( false );
    }

    /**
     * Set the starting value of the PC.  This indicates where to begin
     * symbolic simulation, and is typically the entry point for a function.
     */
    public void setStartPC( SimulatorValue v ) {
        opts.setStartPc( v.getValueRep() );
    }

    /**
     * Set the value to be used as the return address.  This should not be
     * the location of any valid instruction in the program.  Symoblic simulation
     * will end when control passes to this value.
     */
    public void setReturnAddress( SimulatorValue v ) {
        opts.setReturnAddress( v.getValueRep() );
    }

    /**
     * Set the starting value of the stack pointer.  This should be in an area
     * of memory that does not overlap with the program's expected data segment,
     * heap, etc.  The stack will grow either up or down from here depending on
     * the convention of the compiled program.
     */
    public void setStartStack( SimulatorValue v ) {
        opts.setStartStack( v.getValueRep() );
    }

    /**
     * Set the program to simulate.  This should be the function handle for
     * the translated CFG to verify.
     */
    public void setProgram( Procedure proc ) {
        opts.setProgram( proc.getHandle().getValueRep() );
    }

    /**
     * Set the output directory.  The crucible server will produce it's output
     * into the given directory path.  
     */
    public void setOutputDirectory( String path ) {
        opts.setOutputDirectory( path );
    }

    /**
     * Should the crucible server produce separate files for each generated proof obligation?
     * If true, a separte SAWCore file will be generated for each safety condition and postcondition
     * statement.  If false, all conditions will be combined together into a single file.
     *
     * This is a tradeoff.  Separate obligations may allow solvers to make better progress on individual goals.
     * However, a single file allows better subterm sharing in the case that separate goals refer to the same
     * subterms (which is fairly common).
     */ 
    public void setSeparateObligations( boolean b ) {
        opts.setSeparateObligations( b );
    }

    public Protos.VerificationSimulateOptions getRep() {
        return opts.build();
    }
}
