package com.galois.crucible.cfg;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.Type;

/**
 * A block that accepts an argument from the previous block as an input.
 *
 * Used for pattern matching.
 */
public final class LambdaBlock extends SomeBlock {
    private final LambdaArg arg;

    /** Internal method for creating a lambda block. */
    LambdaBlock(Procedure p, int index, Type param_type) {
        super(p, index);
        this.arg = new LambdaArg(index, param_type);
    }

    /**
     * Get argument passed to this block.
     * @return the argument.
     */
    public LambdaArg getArg() {
        return arg;
    }

    /**
     * Return type of argument expected by block.
     * @return the type
     */
    public Type getArgType() {
        return arg.type();
    }

    public Protos.Block getBlockRep() {
        if (termStmt == null) {
            String msg = "This block is unterminated.";
            if( block_description != null ) {
                msg = msg + " " + block_description;
            }
            throw new IllegalStateException(msg);
        }

        return Protos.Block.newBuilder()
            .setIsLambda(true)
            .setLambdaType(arg.type().getTypeRep())
            .addAllStatement(statements)
            .setTermStmt(termStmt)
            .setPos( pos )
            .build();
    }
}
