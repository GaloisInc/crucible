package com.galois.crucible.cfg;
import com.galois.crucible.proto.Protos;

/**
 * A contiguous set of instructions in a control flow graph.
 */
public final class Block extends SomeBlock {
    /**
     * Internal method for creating a block
     */
    Block(Procedure procedure, int block_index) {
        super(procedure, block_index);
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
            .addAllStatement(statements)
            .setTermStmt(termStmt)
            .setPos( pos )
            .build();
    }

}
