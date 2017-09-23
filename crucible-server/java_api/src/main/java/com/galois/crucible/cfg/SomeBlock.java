package com.galois.crucible.cfg;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import com.galois.crucible.BitvectorValue;
import com.galois.crucible.BoolValue;
import com.galois.crucible.IntegerValue;
import com.galois.crucible.NatValue;
import com.galois.crucible.FunctionHandle;
import com.galois.crucible.proto.Protos;
import com.galois.crucible.RationalValue;
import com.galois.crucible.SimulatorValue;
import com.galois.crucible.StringValue;
import com.galois.crucible.Type;
import com.galois.crucible.Typed;
import com.galois.crucible.ValueCreator;

/**
 * Common base class for blocks that expect an argument, and blocks that do not.
 */
public abstract class SomeBlock extends ValueCreator<Expr> {
    private final Procedure procedure;
    /** The index of this block in the CFG. */
    private final int block_index;

    protected final ArrayList<Protos.Statement> statements;

    public String block_description;

    /** Position of this block */
    protected Protos.Position pos;

    /** Current position used when adding statements */
    protected Protos.Position currentPos;

    /**
     * The terminal statement of this block or <code>null</code>
     * if it has not been defined.
     */
    protected Protos.TermStmt termStmt;

    /**
     * Internal method for creating a block
     */
    SomeBlock(Procedure procedure, int block_index) {
        this.procedure = procedure;
        this.block_index = block_index;
        this.statements = new ArrayList<Protos.Statement>();
        this.termStmt = null;
        this.pos = procedure.getPosition();
    }

    /**
     * Get control-flow graph that this block is part of.
     */
    public Procedure getProcedure() {
        return procedure;
    }

    /** Set the position */
    public void setPosition( Position pos )
    {
        if( pos == null ) {
            throw new IllegalArgumentException("pos cannot be null");
        }
        this.pos = pos.getPosRep();
    }

    public void setCurrentPosition( Position pos )
    {
        this.currentPos = pos.getPosRep();
    }

    // Check value is non-null and have type equal to tp.
    private static void checkTypeEquals(String nm, Typed v, Type tp) {
        if (v == null) {
            String msg = String.format("%s must not be null.", nm);
            throw new NullPointerException(msg);
        }
        if (!v.type().equals(tp)) {
            String msg = String.format("%s has incorrect type. Expected %s, but got %s", nm, tp.toString(), v.type().toString());
            throw new IllegalArgumentException(msg);
        }
    }

    // Check that f is a function that expects the given arguments.
    // Returns type of result of f.
    private static Type checkFunctionArgs(Expr f, Expr[] args) {

        if (f == null) throw new NullPointerException("f");

        Type f_type = f.type();

        if (!f_type.isFunctionHandle()) {
            throw new IllegalArgumentException("function does not have correct type.");
        }

        int cnt = f_type.getFunctionArgumentCount();
        if (cnt != args.length) {
            throw new IllegalArgumentException("Incorrect number of arguments.");
        }

        for (int i = 0; i != cnt; ++i) {
            Expr arg = args[i];
            Type type = f_type.getFunctionArgumentType(i);
            checkTypeEquals("arg", arg, type);
        }
        return f_type.getFunctionReturnType();
    }

    private void addStatement(Protos.Statement.Builder stmt) {
        if (this.termStmt != null) {
            throw new IllegalStateException("This block has already been terminated.");
        }

        if( currentPos != null ) {
            stmt = stmt.setPos( currentPos );
        }
        statements.add(stmt.build());
    }

    private
    StatementResult addEvalStmt(Type result_type,
                                Protos.Statement.Builder stmt) {

        long stmt_index = statements.size();
        // Add statement to list.
        addStatement(stmt);
        // Get return value.
        return new StatementResult(block_index, stmt_index, result_type);
    }

    private void setTermStmt(Protos.TermStmt.Builder termStmt) {
        if (this.termStmt != null) {
            throw new IllegalStateException("This block has already been terminated.");
        }

        if( currentPos != null ) {
            termStmt = termStmt.setPos( currentPos );
        }

        this.termStmt = termStmt.build();
    }


    public Expr boolLiteral( boolean val )
    {
        if( val ) {
            return BoolValue.TRUE;
        } else {
            return BoolValue.FALSE;
        }
    }

    public Expr bvLiteral( long width, BigInteger val )
    {
        return new BitvectorValue( width, val );
    }

    public Expr natLiteral( BigInteger val )
    {
        return new NatValue( val );
    }

    public Expr callHandle( FunctionHandle hdl, Object... args )
    {
        return call( hdl, Arrays.copyOf( args, args.length, Expr[].class ) );
    }

    protected
    Expr applyPrimitive(Type result_type,
                        Protos.PrimitiveOp op,
                        Object... args) {
        Protos.Statement.Builder b
            = Protos.Statement.newBuilder()
            .setCode(Protos.StatementCode.ExecPrimitive)
            .setPrimOp(op)
            .setResultType(result_type.getTypeRep());
        for (Object e : args) {
            b.addExpr(((Expr) e).getExprRep());
        }
        // Add statement to list.
        return addEvalStmt(result_type, b);
    }

    /**
     * Read the current value of the register.
     */
    public Expr read(Reg r) {
        if (r == null) throw new NullPointerException("r");
        return addEvalStmt(r.type(),
                           Protos.Statement.newBuilder()
                           .setCode(Protos.StatementCode.ReadReg)
                           .setReg(r.index()));
    }

    /**
     * Write the expression to the register.
     */
    public void write(Reg lhs, Expr rhs) {
        if (lhs == null) throw new NullPointerException("lhs");
        checkTypeEquals("rhs", rhs, lhs.type());
        addStatement(Protos.Statement.newBuilder()
                     .setCode(Protos.StatementCode.WriteReg)
                     .setReg(lhs.index())
                     .addExpr(rhs.getExprRep()));
    }

    /**
     * Call a function with the given arguments.
     */
    public Expr call(Expr f, Expr... args) {
        Type result_type = checkFunctionArgs(f, args);
        Protos.Statement.Builder b
            = Protos.Statement.newBuilder()
            .setCode(Protos.StatementCode.Call)
            .addExpr(f.getExprRep())
            .setResultType(result_type.getTypeRep());
        for (Expr e : args) {
            b.addExpr(e.getExprRep());
        }

        return addEvalStmt(result_type, b);
    }

    /**
     * Print a string.
     * @param msg String to print
     */
    public void print(Expr msg) {
        checkTypeEquals("msg", msg, Type.STRING);

        addStatement(Protos.Statement.newBuilder()
                     .setCode(Protos.StatementCode.Print)
                     .addExpr(msg.getExprRep()));
    }

    /**
     * Print a string.
     * @param msg String literal to print
     */
    public void print(String msg) {
        print( new StringValue(msg) );
    }
    /**
     * Add assertion statement.
     */
    public void assertCond(Expr c, Expr m) {
        checkTypeEquals("c", c, Type.BOOL);
        checkTypeEquals("m", m, Type.STRING);

        addStatement(Protos.Statement.newBuilder()
                     .setCode(Protos.StatementCode.Assert)
                     .addExpr(c.getExprRep())
                     .addExpr(m.getExprRep()));
    }


    /**
     * End block with jump.
     */
    public void jump(Block lbl) {
        setTermStmt(Protos.TermStmt.newBuilder()
                    .setCode(Protos.TermStmtCode.JumpTermStmt)
                    .addBlock(((SomeBlock) lbl).block_index));
    }

    /**
     * End block with branch.
     */
    public void branch(Expr c, Block t, Block f) {
        if (c == null) throw new NullPointerException("c");
        if (!c.type().equals(Type.BOOL))
            throw new IllegalArgumentException("Branch condition must be Boolean.");

        setTermStmt(Protos.TermStmt.newBuilder()
                    .setCode(Protos.TermStmtCode.BranchTermStmt)
                    .addExpr(c.getExprRep())
                    .addBlock(((SomeBlock) t).block_index)
                    .addBlock(((SomeBlock) f).block_index));
    }

    /**
     * Return from the procedure with the given value.
     * @param v Return value
     */
    public void returnExpr(Expr v) {
        Type return_type = procedure.getHandle().getReturnType();
        checkTypeEquals("v", v, return_type);

        setTermStmt(Protos.TermStmt.newBuilder()
                    .setCode(Protos.TermStmtCode.ReturnTermStmt)
                    .addExpr(v.getExprRep()));
    }

    /**
     * Terminate block with an error message.
     * @param msg String to print
     */
    public void reportError(Expr msg) {
        checkTypeEquals("msg", msg, Type.STRING);
        setTermStmt(Protos.TermStmt.newBuilder()
                    .setCode(Protos.TermStmtCode.ErrorTermStmt)
                    .addExpr(msg.getExprRep()));
    }

    /**
     * Terminate block with a tail call.
     * @param f Function to call
     * @param args Arguments to function
     */
    public void tailCall(Expr f, Expr ... args) {
        Type f_returnType = checkFunctionArgs(f, args);
        Type returnType = procedure.getHandle().getReturnType();
        if (!returnType.equals(f_returnType)) {
            throw new IllegalArgumentException(
              "Tail called function must return same type of result as caller.");
        }

        Protos.TermStmt.Builder b
            = Protos.TermStmt.newBuilder()
            .setCode(Protos.TermStmtCode.TailCallTermStmt)
            .addExpr(f.getExprRep());
        for (Expr e : args) {
            b.addExpr(e.getExprRep());
        }
        setTermStmt(b);
    }

    /**
     * Pattern match on whether the expression, which should be a
     * maybe value has an expression.
     */
    public void switchMaybe(Expr v, LambdaBlock j, Block n) {
        if (v == null) throw new NullPointerException("m");
        Type v_type = v.type();
        if (!v_type.isMaybe()) {
            throw new IllegalArgumentException("Expression must be maybe type.");
        }
        if (!(v_type.equals(j.getArgType()))) {
            throw new IllegalArgumentException("Block must match expected type.");
        }
        setTermStmt(Protos.TermStmt.newBuilder()
                    .setCode(Protos.TermStmtCode.SwitchMaybeTermStmt)
                    .addExpr(v.getExprRep())
                    .addBlock(((SomeBlock) j).block_index)
                    .addBlock(((SomeBlock) n).block_index));
    }

    public abstract Protos.Block getBlockRep();
}
