package com.galois.crucible.cfg;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import com.galois.crucible.Simulator;
import com.galois.crucible.FunctionHandle;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.Type;

/**
 * A control-flow-graph and handle associated to it.
 */
public final class Procedure {
    private final FunctionHandle handle;

    /** List of expressions in function. */
    private final List<FunctionArg> arguments;

    /** List of all registers allocated in Cfg. */
    private final List<Reg> registers;

    /** Entry block for this procedure. */
    private final Block entryBlock;

    /** List of all blocks allocated in Cfg. */
    private final List<SomeBlock> blocks;

    /** Position of this procedure */
    private Protos.Position pos;

    /**
     * Create a new control-flow graph with a freshly-allocated function handle.
     * @param sim simulator object
     * @param displayName name attached to the funtion handle
     * @param argTypes types of the arguments to the function
     * @param returnType type of the return value of the function
     */
    public Procedure( Simulator sim, String displayName, Type[] argTypes, Type returnType )
        throws IOException
    {
        this( sim.newHandle( displayName, argTypes, returnType ) );
    }

    /**
     * Create a new control-flow graph.
     * @param h the handle associated to procedure
     */
    public Procedure(FunctionHandle h) {
        this.handle = h;
        this.pos = new InternalPosition( h.getDisplayName() ).getPosRep();

        int argCount = h.getArgCount();
        this.arguments = new ArrayList<FunctionArg>(argCount);
        // Populate argument list.
        for (int i = 0; i != argCount; ++i) {
            arguments.add(new FunctionArg(i, h.getArgType(i)));
        }

        this.registers = new ArrayList<Reg>();
        this.entryBlock = new Block(this, 0);
        this.blocks = new ArrayList<SomeBlock>();
        this.blocks.add(entryBlock);
    }

    /**
     * Get the handle associated with this procedure.
     * @return the handle
     */
    public FunctionHandle getHandle() {
        return handle;
    }

    /**
     * Get first block.
     * @return the block
     */
    public Block getEntryBlock() {
        return entryBlock;
    }

    /**
     * Return number of arguments expected by procedure.
     * @return the number of arguments
     */
    public int getArgCount() {
        return handle.getArgCount();
    }

    /**
     * The the position for this procedure.
     */
    public void setPosition( Position pos )
    {
        this.pos = pos.getPosRep();
    }

    public Protos.Position getPosition()
    {
        return this.pos;
    }

    /**
     * Returns expression representing argument for function.
     * @param i the index of the argument.
     * @return the argument.
     */
    public FunctionArg getArg(int i) {
        if (!(0 <= i && i < arguments.size())) {
            throw new IllegalArgumentException("Bad argument index.");
        }
        return arguments.get(i);
    }

    /**
     * Allocate a new register.
     * @param tp the type of the register.
     * @return the register
     */
    public Reg newReg(Type tp) {
        Reg r = new Reg(registers.size(), tp);
        registers.add(r);
        return r;
    }

    /**
     * Create a new basic block.
     * @return the block
     */
    public Block newBlock() {
        Block b = new Block(this, blocks.size());
        blocks.add(b);
        return b;
    }

    /**
     * Create a new block that expects an argument when jumped to.
     * @param param_type the type of the argument expected by block.
     * @return the block
     */
    public LambdaBlock newLambdaBlock(Type param_type) {
        LambdaBlock b = new LambdaBlock(this, blocks.size(), param_type);
        blocks.add(b);
        return b;
    }

    /**
     * Get the Protocol buffer representation.
     * @return the representation object.
     */
    public Protos.Cfg getCfgRep() {
        Protos.Cfg.Builder b
            = Protos.Cfg.newBuilder()
            .setHandleId(handle.getUniqueId())
            .setPos( pos );
        for (Reg r : registers) {
            b.addRegister(r.type().getTypeRep());
        }
        for (SomeBlock block : blocks) {
            b.addBlock(block.getBlockRep());
        }
        return b.build();

    }
}
