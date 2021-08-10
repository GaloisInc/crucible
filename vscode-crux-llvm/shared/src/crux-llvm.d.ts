/* eslint-disable @typescript-eslint/semi */
/* eslint-disable quotes */

type CruxLLVMLogging = ILoggingCrux | ILoggingCruxLLVM;

interface ILoggingCrux {
  tag: "LoggingCrux";
  contents: CruxLogMessage;
}

interface ILoggingCruxLLVM {
  tag: "LoggingCruxLLVM";
  contents: CruxLLVMLogMessage;
}

type CruxLogMessage = IAttemptingProvingVCs | IChecking | IDisablingBranchCoverageRequiresPathSatisfiability | IDisablingProfilingIncompatibleWithPathSplitting | IEndedGoal | IFoundCounterExample | IHelp | IPathsUnexplored | IProofObligations | ISimulationComplete | ISimulationTimedOut | ISkippingUnsatCoresBecauseMCSatEnabled | IStartedGoal | ITotalPathsExplored | IUnsupportedTimeoutFor | IVersion;

interface IAttemptingProvingVCs {
  tag: "AttemptingProvingVCs";
}

interface IChecking {
  tag: "Checking";
  contents: string[];
}

interface IDisablingBranchCoverageRequiresPathSatisfiability {
  tag: "DisablingBranchCoverageRequiresPathSatisfiability";
}

interface IDisablingProfilingIncompatibleWithPathSplitting {
  tag: "DisablingProfilingIncompatibleWithPathSplitting";
}

interface IEndedGoal {
  tag: "EndedGoal";
  contents: number;
}

interface IFoundCounterExample {
  tag: "FoundCounterExample";
}

interface IHelp {
  tag: "Help";
  contents: string;
}

interface IPathsUnexplored {
  tag: "PathsUnexplored";
  contents: number;
}

interface IProofObligations {
  tag: "ProofObligations";
  contents: SerializedLogProofObligation[];
}

interface ISimulationComplete {
  tag: "SimulationComplete";
}

interface ISimulationTimedOut {
  tag: "SimulationTimedOut";
}

interface ISkippingUnsatCoresBecauseMCSatEnabled {
  tag: "SkippingUnsatCoresBecauseMCSatEnabled";
}

interface IStartedGoal {
  tag: "StartedGoal";
  contents: number;
}

interface ITotalPathsExplored {
  tag: "TotalPathsExplored";
  contents: number;
}

interface IUnsupportedTimeoutFor {
  tag: "UnsupportedTimeoutFor";
  contents: string;
}

interface IVersion {
  tag: "Version";
  contents: [string, string];
}

type CruxLLVMLogMessage = IBreakpoint | IClangInvocation | IExecutable | IFailedToBuildCounterexampleExecutable | ISimulatingFunction | IUsingPointerWidthForFile;

interface IBreakpoint {
  tag: "Breakpoint";
  contents: string;
}

interface IClangInvocation {
  tag: "ClangInvocation";
  contents: string[];
}

interface IExecutable {
  tag: "Executable";
  contents: string;
}

interface IFailedToBuildCounterexampleExecutable {
  tag: "FailedToBuildCounterexampleExecutable";
}

interface ISimulatingFunction {
  tag: "SimulatingFunction";
  contents: string;
}

interface IUsingPointerWidthForFile {
  tag: "UsingPointerWidthForFile";
  contents: [number, string];
}

type SerializedLogProofObligation = ISerializedLogProofObligation;

interface ISerializedLogProofObligation {
  labeledPred: string;
  labeledPredMsg: string;
}
