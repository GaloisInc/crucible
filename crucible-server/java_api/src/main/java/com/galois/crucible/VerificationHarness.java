package com.galois.crucible;

import com.galois.crucible.proto.Protos;

public class VerificationHarness {
    private Protos.VerificationHarness.Builder harness;
    private StateSpecification innerPrestate;
    private StateSpecification innerPoststate;

    private static Protos.VariableSpecification newVar( String name, int width ) {
        return Protos.VariableSpecification.newBuilder().
            setName(name).
            addDimension(width).
            build();
    }

    private static Protos.VariableSpecification newVar( String name, int elems, int width ) {
        return Protos.VariableSpecification.newBuilder().
            setName(name).
            addDimension(elems).
            addDimension(width).
            build();
    }

    private static Protos.VariableBinding newVariableBinding( Protos.VariableReference ref, String expr ) {
        return Protos.VariableBinding.newBuilder().
            setVar( ref ).
            setExpr( expr ).
            build();
    }

    private static Protos.RegisterAssignment newRegisterAssignment( long offset, Protos.VariableReference value ) {
        return Protos.RegisterAssignment.newBuilder().
            setRegOffset( offset ).
            setValue( value ).
            build();
    }

    private static Protos.MemoryAssignment newMemoryAssignment( Protos.VariableReference base,
                                                                long offset,
                                                                Protos.VariableReference value ) {
        return Protos.MemoryAssignment.newBuilder().
            setBase( base ).
            setOffset( offset ).
            setValue( value ).
            build();
    }

    public static Protos.VariableReference userVar( String name ) {
        return Protos.VariableReference.newBuilder().
            setCode( Protos.VariableReferenceCode.UserVar ).
            setVarName( name ).
            build();
    }

    public static Protos.VariableReference stackVar() {
        return Protos.VariableReference.newBuilder().
            setCode( Protos.VariableReferenceCode.StackPointerVar ).
            build();
    }

    public static Protos.VariableReference returnVar() {
        return Protos.VariableReference.newBuilder().
            setCode( Protos.VariableReferenceCode.ReturnAddressVar ).
            build();
    }

    public class StateSpecification {
        Protos.StateSpecification.Builder specBuilder;

        StateSpecification( Protos.StateSpecification.Builder specBuilder ) {
            this.specBuilder = specBuilder;
        }

        public void addVar( String name, int width ) {
            specBuilder.addVariable( newVar( name, width ) );
        }

        public void addVar( String name, int elems, int width ) {
            specBuilder.addVariable( newVar( name, elems, width ) );
        }
        
        public void assignRegister( long offset, Protos.VariableReference var ) {
            specBuilder.addRegisterAssignment( newRegisterAssignment( offset, var ) );
        }

        public void assignMemory( Protos.VariableReference base,
                                  long offset,
                                  Protos.VariableReference value ) {
            specBuilder.addMemoryAssignment( newMemoryAssignment( base, offset, value ) );
        }

        public void bindVariable( Protos.VariableReference var, String expr ) {
            specBuilder.addVariableBinding( newVariableBinding( var, expr ) );
        }

        public void assertCondition( String expr ) {
            specBuilder.addCondition( expr );
        }
    }

    public VerificationHarness(String name) {
        this.harness = Protos.VerificationHarness.newBuilder();
        harness.setName(name);
        this.innerPrestate  = new StateSpecification( harness.getPrestateSpecificationBuilder() );
        this.innerPoststate = new StateSpecification( harness.getPoststateSpecificationBuilder() );
    }
    
    public Protos.VerificationHarness getRep() {
        return harness.build();
    }
    
    public StateSpecification prestate() {
        return innerPrestate;
    }

    public StateSpecification poststate() {
        return innerPoststate;
    }
}
