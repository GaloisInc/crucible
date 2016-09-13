package com.galois.crucible.examples;

import com.galois.crucible.*;
import com.galois.crucible.proto.Protos;
import java.io.IOException;

public class Test {
    public static void main(String[] args) {
        if (args.length != 1) {
            System.err.println("The test server expects a single argument with the path to the server.");
            System.exit(-1);
        }

        try {
            SimpleSimulator s = SimpleSimulator.launchLocal(args[0]);
            System.out.println("client: Started server");
            SimulatorValue x = new IntegerValue(4);
            System.out.format("client: Generated constant: %s\n", x);

            SimulatorValue v = s.freshConstant(VarType.INTEGER);

            SimulatorValue r = s.add(x,x);
            System.out.format("client: Compute x + x: %s\n", r);
            /*
            SatResult r = s.checkSat(s.eq(s.add(x,x), s.natConstant(1)));
            if (r.isSat()) {
                System.out.println("Satisfiable");
                System.out.format("  x: $1%n", r.valueOf(x));
            } else {
                System.out.println("Unsatisfiable");
            }
            */

            s.close();
        } catch (InterruptedException e) {
            System.err.println("Error launching local server:");
            System.err.println(e.getLocalizedMessage());
            System.exit(-1);
        } catch (IOException e) {
            System.err.println("Error launching local server:");
            System.err.println(e.getLocalizedMessage());
            System.exit(-1);
        }
    }
}
    /*
int main(int argc, char** argv) {

 // Create a simulator object for storing the simulator state.
 simulator* s = csim_new_simulator();

 // Create a new handle
 handle* add_handle =
   csim_new_handle(s, "write_add_comm", 1, csim_string_type(), csim_unit_type());

 // Create a control flow graph for the handle.
 cfg* g = csim_new_cfg(add_handle);

 // Get the entry block for g.
 block* b = csim_cfg_entry_block(g);

 // Get an expression representing the first argument.
 expr* path = csim_cfg_arg(g, 0);

 // Create two registers for storing 32-bit bitvector.s
 reg* x = csim_new_reg(g, csim_bv_type(32));
 reg* y = csim_new_reg(g, csim_bv_type(32));

 // Create two symbolic variables for.
 handle* mk_symbolic = csim_handleof_symbolic_uint(s);
 csim_append_call(b, x, mk_symbolic, csim_nat_lit(32));
 csim_append_call(b, y, mk_symbolic, csim_nat_lit(32));

// Question: why don't we get something back from this?
   // - or is reg * a flag that gets set
// Goal: mere mortals should be able to figure this out.

 // Generate expression asserting x + y == y + x.
 expr* eq = csim_bv_eq(csim_bv_add(csim_reg_expr(x), csim_reg_expr(y)),
                       csim_bv_add(csim_reg_expr(y), csim_reg_expr(x)));
// this makes sense -- we get an expression back - but why can't we say:

// expr *x = csim_new_ivar(32)
// expr *y = csim_new_ivar(32)
// expr *eq = csim_bv_eq(csim_bv_add(x,y), ... )
// ??

 // Write expresison to SMT lib.
 csim_append_call(b, x, csim_handleof_write_smtlib2(s), path, eq);
// why the X above? are we back to register variables?
// it would be nice to not have to track both symbolic variables and regular ones...
// "what is a regular variable" - why is a reg * different from an expr.
JHX - regs can be modified, exprs can not - basic blocks coming soon
// can we hide distinctions.


 // Return from procedure.
 csim_end_return(b, csim_unit_expr());

 // Tell simulator to use CFG during simulation of add_handle.
 csim_use_cfg(s, g);

 // Symbolically simulator the write_add_comm function.
 csim_run_call(s, add_handle, csim_string_lit("add_comm.smt"));

 // Free the symbolic simulator.
 csim_free_simulator(s);
 return 0;
}
    */
